Require Import List.
Require Import Arith.

Require Export C.

(** * CU for "Clean Up" *)

Definition cleanup := nat.

Inductive expr : Set :=
| App : var -> vars -> cleanup -> expr
| Constr : constructor -> vars -> cleanup -> expr
| Letrec : list (gen_lambda_form (Expr := expr)) -> expr -> expr
| Case : expr -> list (gen_alt (Expr := expr)) -> expr.

Definition lambda_form := gen_lambda_form (Expr := expr).

Definition alt := gen_alt (Expr := expr).

Definition alts := list alt.

Theorem expr_ind2 :
forall (P : expr -> Prop)
  (APP    : forall x xs cu, P (App x xs cu))
  (CONSTR : forall C xs cu, P (Constr C xs cu))
  (LETREC : forall e lfs
    (EXPR : P e)
    (LF   : forall lf
      (IN : In lf lfs),
      match lf with Lf _ _ _ f => P f end),
    P (Letrec lfs e))
  (CASE   : forall e als
    (EXPR : P e)
    (ALS  : forall al
      (IN : In al als),
      match al with Alt _ f => P f end),
    P (Case e als))
  (e : expr), P e.
Proof.
intros.
revert e.
refine (fix rec (e : expr) : P e := _).
destruct e.
(* App *)
apply APP.
(* Constr *)
apply CONSTR.
(* Letrec *)
apply LETREC.
apply rec.
induction l.
intros; inversion IN.
intros; simpl in IN.
inversion IN.
rewrite <- H; destruct a; apply rec.
apply IHl.
apply H.
(* Case *)
apply CASE.
apply rec.
induction l.
intros; inversion IN.
intros; simpl in IN.
inversion IN.
rewrite <- H; destruct a; apply rec.
apply IHl.
apply H.
Qed.

Hint Resolve eq_nat_dec vars_eq_dec var_eq_dec list_eq_dec.

Lemma length_not_eq :
forall (T : Type) (xs ys : list T)
  (LEN : length xs <> length ys),
  xs <> ys.
Proof with isa.
induction xs; induction ys...
intro; discriminate.
intro; discriminate.
intro.
inversion H; subst.
tauto.
Qed.

Ltac eq_r X := destruct X; [ | let Y := fresh "Y" in
  (right; intro Y; inversion Y; contradiction) ].

Definition expr_eq_dec  : forall a b : expr, {a = b} + {a <> b}.
Proof.
refine (fix rec (a b : expr) {struct a} : {a = b} + {a <> b} := _).
destruct a; destruct b; try (right; intro; discriminate).
(* App *)
eq_r (var_eq_dec v v1).
eq_r (vars_eq_dec v0 v2).
eq_r (eq_nat_dec c c0).
subst; left; reflexivity.
(* Constr *)
eq_r (eq_nat_dec c c1).
eq_r (vars_eq_dec v v0).
eq_r (eq_nat_dec c0 c2).
subst; left; reflexivity.
(* Letrec *)
destruct (eq_nat_dec (length l) (length l0)) as [ LENEQ | NEQ ]; [ |
  apply length_not_eq in NEQ; right; intro H; inversion H; contradiction ].
revert l0 LENEQ.
induction l; intros.
  (* nil *)
induction l0; try discriminate.
assert (EQ := rec a b).
destruct EQ;
[ left; f_equal; assumption
| right; intro H; inversion H; contradiction ].
  (* cons *)
destruct l0; try discriminate.
inversion LENEQ as [ LENEQ2 ].
destruct (IHl l0 LENEQ2) as [ TAILEQ | TAILNEQ ]; [ |
  right; intro H; inversion H; subst; intuition ].
destruct a0.
destruct g.
assert (HEADEQ := rec e e0).
destruct HEADEQ as [ HEADEQ | HEADNEQ ].
eq_r (upd_flag_eq_dec u u0).
eq_r (vars_eq_dec v v0).
eq_r (eq_nat_dec b0 b1).
subst.
left; inversion TAILEQ; subst; f_equal; reflexivity.
right; intro H; inversion H; contradiction.
(* Case *)
destruct (eq_nat_dec (length l) (length l0)) as [ LENEQ | NEQ ]; [ |
  apply length_not_eq in NEQ; right; intro H; inversion H; contradiction ].
revert l0 LENEQ.
induction l; intros.
  (* nil *)
induction l0; try discriminate.
assert (EQ := rec a b).
destruct EQ;
[ left; f_equal; assumption
| right; intro H; inversion H; contradiction ].
  (* cons *)
destruct l0; try discriminate.
inversion LENEQ as [ LENEQ2 ].
destruct (IHl l0 LENEQ2) as [ TAILEQ | TAILNEQ ]; [ |
  right; intro H; inversion H; subst; intuition ].
destruct a0.
destruct g.
assert (HEADEQ := rec e e0).
destruct HEADEQ as [ HEADEQ | HEADNEQ ].
eq_r (eq_nat_dec b0 b1).
subst.
left; inversion TAILEQ; subst; f_equal; reflexivity.
right; intro H; inversion H; contradiction.
Qed.

Definition alt_eq_dec  : forall a b : alt, {a = b} + {a <> b}.
Proof.
decide equality.
apply expr_eq_dec.
Qed.

Definition lf_eq_dec : forall a b : lambda_form, {a = b} + {a <> b}.
Proof.
decide equality.
apply expr_eq_dec.
apply upd_flag_eq_dec.
Qed.

Theorem expr_rec2 :
forall (P : expr -> Set)
  (APP    : forall x xs cu, P (App x xs cu))
  (CONSTR : forall C xs cu, P (Constr C xs cu))
  (LETREC : forall e lfs
    (EXPR : P e)
    (LF   : forall lf
      (IN : In lf lfs),
      match lf with Lf _ _ _ f => P f end),
    P (Letrec lfs e))
  (CASE   : forall e als
    (EXPR : P e)
    (ALS  : forall al
      (IN : In al als),
      match al with Alt _ f => P f end),
    P (Case e als))
  (e : expr), P e.
Proof.
intros.
revert e.
refine (fix rec (e : expr) : P e := _).
destruct e.
(* App *)
apply APP.
(* Constr *)
apply CONSTR.
(* Letrec *)
apply LETREC.
apply rec.
induction l.
intros; inversion IN.
intros; simpl in IN.
destruct (In_dec lf_eq_dec lf l) as [ I | NI ].
apply IHl; apply I.
assert (H : a = lf).
  inversion IN.
  apply H.
  contradiction.
rewrite <- H; destruct a; apply rec.
(* Case *)
apply CASE.
apply rec.
induction l.
intros; inversion IN.
intros; simpl in IN.
destruct (In_dec alt_eq_dec al l) as [ I | NI ].
apply IHl; apply I.
assert (H : a = al).
  inversion IN.
  apply H.
  contradiction.
rewrite <- H; destruct a; apply rec.
Qed.

(* Configurations *)

Definition closure := gen_closure (Expr := expr).

Definition heap := gen_heap (Clo := closure).

Inductive config : Set :=
| Config : heap -> expr -> env -> argstack -> addresses -> config
| Enter : heap -> address -> argstack -> env -> config.

Notation " << a , b , c , d , e >> " := (Config a b c d e) (at level 70).
Notation " << a , b , c , d >> " := (Enter a b c d) (at level 70).

Definition env_from_config (c : config) : env :=
match c with
| Config _ _ e _ _ => e
| Enter _ _ _ e => e
end.

Definition x := << fun x => None, Constr 5 nil (0), nil, nil, nil >>.

Definition make_cons (C : constructor) (addrs : addresses) : closure :=
(Lf_n nil 0 (Constr C (map C_ind (from 0 (length addrs))) 0), addrs).

Definition make_pap (q : address) (addrs : addresses) : closure :=
(Lf_n nil 0 (App (C_ind 0) (map C_ind (from 1 (length addrs))) 0), q::addrs).

Lemma map_env_make :
forall (addrs : addresses) xs,
map_env nil (xs++addrs) (map C_ind (from (length xs) (length addrs))) = Some addrs.
Proof with isa; try discriminate.
intros.
remember (map C_ind (from (length xs) (length addrs))) as ys.
generalize dependent xs; generalize dependent addrs; induction ys...
destruct addrs...
destruct addrs...
remember (map_env nil (xs ++ a0 :: addrs) ys) as MEM; destruct MEM...
inversion Heqys; subst; clear Heqys...
rewrite C.nth_app; repeat f_equal.
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
Proof with isa.
intros.
apply (map_env_make args (p::nil))...
Qed.

Inductive value : Set :=
| Val_con : heap -> constructor -> addresses -> value
| Val_pap : heap -> address -> addresses -> value.

(* Semantics *)

Reserved Notation " a ↓ b " (at level 70, no associativity).

Inductive Sem : config -> (value * env) -> Prop :=

| Cons : forall Gamma C xs sigma clo addrs cleanup
  (MAPENV : map_env sigma clo xs = Some addrs),
  << Gamma, Constr C xs (cleanup), sigma, nil, clo >> ↓ (Val_con Gamma C addrs, (skipn cleanup sigma))

| Accum : forall Gamma x xs sigma args clo p new_args Value cleanup
  (MAPENV  : map_env sigma clo xs = Some new_args)
  (LOOKUP  : look_up sigma clo x = Some p)
  (PREMISE : << Gamma, p, new_args++args, skipn cleanup sigma >> ↓ Value),
  << Gamma, App x xs (cleanup), sigma, args, clo >> ↓ Value

| App1 : forall Gamma p args clovars bind e some_clo sigma 
  (ONHEAP : Gamma p = Some (Lf_n clovars bind e, some_clo))
  (LENGTH : bind > length args),
  << Gamma, p, args, sigma >> ↓ (Val_pap Gamma p args, sigma)

| App2 : forall Gamma p args Value e bind clo clovars sigma
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, clo))
  (LENGTH  : bind <= length args)
  (PREMISE : << Gamma, e, firstn bind args ++ sigma, skipn bind args, clo >> ↓ Value),
  << Gamma, p, args, sigma >> ↓ Value

| App3 : forall Gamma p C addrs clovars Delta e clo sigma theta
  (ONHEAP  : Gamma p = Some (Lf_u clovars 0 e, clo))
  (PREMISE : << (clog Gamma p), e, sigma, nil, clo >> ↓ (Val_con Delta C addrs, theta)),
  << Gamma, p, nil, sigma >> ↓ (Val_con (set Delta p (make_cons C addrs)) C addrs, theta)

| App4 : forall Gamma p args Value q addrs e clovars clo_e Delta sigma theta
  (ONHEAP1 : Gamma p = Some (Lf_u clovars 0 e, clo_e))
  (LEFT    : << (clog Gamma p), e, sigma, nil, clo_e >> ↓ (Val_pap Delta q addrs, theta))
  (RIGHT   : << set Delta p (make_pap q addrs), q, addrs++args, theta >> ↓ Value),
  << Gamma, p, args, sigma >> ↓ Value

| Let : forall Gamma e lfs sigma current_clo closures Value addrs args
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) current_clo lfs = Some closures)
  (PREMISE : << alloc Gamma addrs closures, e, addrs++sigma, args, current_clo >> ↓ Value),
  << Gamma, Letrec lfs e, sigma, args, current_clo >> ↓ Value

| Case_of : forall Gamma e als sigma clo Value bind Delta e0 C addrs args theta
  (SELECT : nth C als = Some (Alt bind e0))
  (* NO LENGTH !!! *)
  (LEFT   : << Gamma, e, sigma, nil, clo >> ↓ (Val_con Delta C addrs, theta))
  (RIGHT  : << Delta, e0, addrs++theta, args, clo >> ↓ Value),
  << Gamma, Case e als, sigma, args, clo >> ↓ Value

where " a ↓ b " := (Sem a b).
