Require Import List.
Require Import Arith.

Require Export Common.

(** * C for "Closures" *)

Inductive expr : Set :=
| App : var -> vars -> expr
| Constr : constructor -> vars -> expr
| Letrec : list (gen_lambda_form (Expr := expr)) -> expr -> expr
| Case : expr -> list (gen_alt (Expr := expr)) -> expr.

Definition lambda_form := gen_lambda_form (Expr := expr).

Definition alt := gen_alt (Expr := expr).

Definition alts := list alt.

(* Configurations *)

Definition closure := gen_closure (Expr := expr).

Definition heap := gen_heap (Clo := closure).

Inductive config : Set :=
| Config : heap -> expr -> env -> argstack -> addresses -> config
| Enter : heap -> address -> argstack -> config.

Notation " << a , b , c , d , e >> " := (Config a b c d e) (at level 70).
Notation " << a , b , c >> " := (Enter a b c) (at level 70).

Definition x := << fun x => None, Constr 5 nil, nil, nil, nil >>.

Definition make_cons (C : constructor) (addrs : addresses) : closure :=
(Lf_n nil 0 (Constr C (map C_ind (from 0 (length addrs)))), addrs).

Definition make_pap (q : address) (addrs : addresses) : closure :=
(Lf_n nil 0 (App (C_ind 0) (map C_ind (from 1 (length addrs)))),
  q::addrs).

Lemma nth_app : forall (T : Set) (a : T) (xs addrs : list T), nth (length xs) (xs ++ a :: addrs) = Some a.
Proof with isa.
induction xs...
Qed.

(** The following lemma I owe to Filip Sieczkowski. *)

Lemma map_env_make :
forall (addrs xs : addresses),
  map_env nil (xs++addrs) (map C_ind (from (length xs) (length addrs)))
    = Some addrs.
Proof with isa; try discriminate.
intros.
remember (map C_ind (from (length xs) (length addrs))) as ys.
generalize dependent xs; generalize dependent addrs; induction ys...
destruct addrs...
destruct addrs...
remember (map_env nil (xs ++ a0 :: addrs) ys) as MEM; destruct MEM...
inversion Heqys; subst; clear Heqys...
rewrite nth_app; repeat f_equal.
assert (hh : map_env nil ((xs ++ a0 :: nil) ++ addrs)
  (map C_ind (from (S (length xs)) (length addrs))) = Some addrs).
apply IHys...
rewrite app_length...
rewrite <- plus_n_Sm; rewrite plus_0_r...
cutrewrite ((xs ++ a0 :: nil) ++ addrs = xs ++ a0 :: addrs) in hh.
rewrite hh in HeqMEM; inversion HeqMEM...
rewrite app_ass...
inversion Heqys; subst; clear Heqys...
assert (hh : map_env nil ((xs ++ a0 :: nil) ++ addrs)
  (map C_ind (from (S (length xs)) (length addrs))) = Some addrs).
apply IHys...
rewrite app_length...
rewrite <- plus_n_Sm; rewrite plus_0_r...
rewrite app_ass in hh...
rewrite hh in HeqMEM; discriminate.
Qed.

Lemma map_env_make_cons :
forall (addrs : addresses),
map_env nil addrs (map C_ind (from 0 (length addrs))) = Some addrs.
Proof with isa.
intro.
apply (map_env_make addrs nil)...
Qed.

Lemma map_env_make_pap :
forall (p : address) (args : addresses),
map_env nil (p :: args) (map C_ind (from 1 (length args))) = Some args.
Proof.
intros.
apply (map_env_make args (p :: nil))...
Qed.

Inductive value : Set :=
| Val_con : heap -> constructor -> addresses -> value
| Val_pap : heap -> address -> addresses -> value.

(* Semantics *)

Reserved Notation " a ↓ b " (at level 70, no associativity).

Inductive Sem : config -> value -> Prop :=

| Cons : forall Gamma C xs sigma clo addrs
  (MAPENV : map_env sigma clo xs = Some addrs),
  << Gamma, Constr C xs, sigma, nil, clo >> ↓ Val_con Gamma C addrs

| Accum : forall Gamma x xs sigma args clo p new_args Value
  (MAPENV  : map_env sigma clo xs = Some new_args)
  (LOOKUP  : look_up sigma clo x = Some p)
  (PREMISE : << Gamma, p, new_args++args >> ↓ Value),
  << Gamma, App x xs, sigma, args, clo >> ↓ Value

| App1 : forall Gamma p args clovars bind e some_clo 
  (ONHEAP : Gamma p = Some (Lf_n clovars bind e, some_clo))
  (LENGTH : bind > length args),
  << Gamma, p, args >> ↓ Val_pap Gamma p args

| App2 : forall Gamma p args Value e bind clo clovars
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, clo))
  (LENGTH  : bind <= length args)
  (PREMISE : << Gamma, e, firstn bind args, skipn bind args, clo >> ↓ Value),
  << Gamma, p, args >> ↓ Value

| App3 : forall Gamma p C addrs clovars Delta e clo
  (ONHEAP  : Gamma p = Some (Lf_u clovars 0 e, clo))
  (PREMISE : << (clog Gamma p), e, nil, nil, clo >> ↓ Val_con Delta C addrs),
  << Gamma, p, nil >> ↓ Val_con (set Delta p (make_cons C addrs)) C addrs

| App4 : forall Gamma p args Value q addrs e clovars clo_e Delta
  (ONHEAP1 : Gamma p = Some (Lf_u clovars 0 e, clo_e))
  (LEFT    : << (clog Gamma p), e, nil, nil, clo_e >> ↓ Val_pap Delta q addrs)
  (RIGHT   : << set Delta p (make_pap q addrs), q, addrs++args >> ↓ Value),
  << Gamma, p, args >> ↓ Value

| Let : forall Gamma e lfs sigma current_clo closures Value addrs args
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) current_clo lfs = Some closures)
  (PREMISE : << alloc Gamma addrs closures, e, addrs++sigma, args, current_clo >> ↓ Value),
  << Gamma, Letrec lfs e, sigma, args, current_clo >> ↓ Value

| Case_of : forall Gamma e als sigma clo Value bind Delta e0 C addrs args
  (SELECT : nth C als = Some (Alt bind e0))
  (LENGTH : bind = length addrs)
  (LEFT   : << Gamma, e, sigma, nil, clo >> ↓ Val_con Delta C addrs)
  (RIGHT  : << Delta, e0, addrs++sigma, args, clo >> ↓ Value),
  << Gamma, Case e als, sigma, args, clo >> ↓ Value

where " a ↓ b " := (Sem a b).

Lemma pap_is_partial :
forall Conf Gamma p addrs
  (EVAL : Conf ↓ Val_pap Gamma p addrs),
exists clovars, exists bind, exists e, exists clo,
   Gamma p = Some (Lf_n clovars bind e, clo)
/\ bind > length addrs.
Proof.
intros.
remember (Val_pap Gamma p addrs) as Value.
induction EVAL; isa; try discriminate.
inversion HeqValue; subst.
exists clovars; exists bind; exists e; exists some_clo.
tauto.
Qed.
