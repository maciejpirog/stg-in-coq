Require Import List.
Require Import Arith.

(** * VM for "Virtual Machine" *)

Require Import CU.
Require Import FB.
Require Import Common.

Inductive code_pointer : Set :=
| CP_user : nat -> code_pointer
| CP_pap : nat -> code_pointer
| CP_cons : constructor -> nat -> code_pointer.

Definition eq_cp_dec : forall c d : code_pointer, {c = d} + {c <> d}.
Proof.
repeat decide equality.
Defined.

Inductive expr : Set :=
| App : var -> vars -> CU.cleanup -> expr
| Constr : constructor -> vars -> CU.cleanup -> expr
| Letrec : list (vars * code_pointer) -> expr -> expr
| Case : expr -> code_pointer -> expr.

Definition lambda_form := gen_lambda_form (Expr := expr).

Definition alt := gen_alt (Expr := code_pointer).

Definition alts := list alt.

Inductive cs_node : Set :=
| CS_expr : expr -> cs_node
| CS_alts : alts -> cs_node
| CS_lf : lambda_form -> cs_node
| CS_None.

Definition code_store := list (code_pointer * cs_node).

Fixpoint find_cs (cs : code_store) (cp : code_pointer) : cs_node :=
match cs with
| nil => CS_None
| (cp0, node) :: cs0 => if eq_cp_dec cp cp0
  then node
  else find_cs cs0 cp
end.

Definition closure := (code_pointer * addresses)%type.

Definition closures := list closure.

Definition heap := address -> option closure.

Inductive config : Set :=
| Config : heap -> expr -> env -> (argstack * FB.fake_bottom)
  -> address -> config
| Enter : heap -> address -> argstack * FB.fake_bottom -> env -> config.

Inductive ret_value : Set :=
| Val_con : heap -> constructor -> addresses -> ret_value
| Val_pap : heap -> address -> addresses -> ret_value.

Definition value := (ret_value * env * (argstack * FB.fake_bottom))%type.

Notation " << a , b , c , d , e >> " := (Config a b c d e) (at level 70).
Notation " << a , b , c , d >> " := (Enter a b c d) (at level 70).

Inductive action : Set :=
| E : config -> action
| A : value -> action.

Inductive stack_elem : Set :=
| K_alt : code_pointer -> FB.fake_bottom -> stack_elem
| K_upd : address -> FB.fake_bottom -> stack_elem.

Definition stack := list stack_elem.

Definition look_up (e : env) (g : heap) (p : address) (v : var)
  : option address :=
match v with
| B_ind n => nth n e 
| C_ind n => match g p with Some (_, clo) => nth n clo | None => None end
end.

Fixpoint map_env (e : env) (g : heap) (a : address) (vs : vars) {struct vs}
  : option addresses :=
match vs with
| nil => Some nil
| x::xs =>
  match map_env e g a xs with
  | Some ps =>
    match look_up e g a x with
    | Some p => Some (p::ps)
    | None => None
    end
  | None => None
  end
end.

Definition set (g : heap) (a : address) (clo : closure) : gen_heap :=
fun (x : address) => if eq_nat_dec x a
  then Some clo
  else g x.

Definition alloc (g : heap) (addrs : addresses) (clos : list closure)
  : heap :=
fold_right (fun (ad : address * closure) (h : gen_heap) =>
  set h (fst ad) (snd ad))
  g (combine addrs clos).

Lemma set_eq :
forall H s v,
  set H s v s = Some v.
Proof with isa.
intros.
unfold set.
destruct (eq_nat_dec)...
tauto.
Qed.

Lemma set_neq :
forall H s v p
  (NEQ : p <> s),
  set H p v s = H s.
Proof with isa.
intros.
unfold set.
destruct eq_nat_dec...
symmetry in e.
intuition.
Qed.

Lemma alloc_in :
forall H vs v lfs lf
  (LEN   : length vs = length lfs)
  (IN    : In v vs)
  (ALLOC : alloc H vs lfs v = Some lf),
  In lf lfs.
Proof with isa.
induction vs...
contradiction.
destruct lfs; try discriminate...
inversion LEN as [ LEN0 ].
destruct (eq_nat_dec a v).
(* eq *)
subst...
unfold alloc in *...
rewrite set_eq in ALLOC.
inversion ALLOC as [ ALLOC0 ]; subst; auto.
(* neq *)
unfold alloc in *...
rewrite set_neq in ALLOC...
right; eapply IHvs; eauto.
fold (alloc H vs lfs) in ALLOC.
inversion IN...
contradiction.
Qed.

Lemma alloc_nin :
forall H vs p
  (NIN : ~ In p vs)
  lfs,
  alloc H vs lfs p = H p.
Proof with isa.
induction vs.
trivial.
assert (NOTIN : forall A p (x : A) xs,
  ~ In p (x :: xs) -> p <> x /\ ~ In p xs).
  isa.
intros.
apply NOTIN in NIN.
destruct NIN as [ NEQ NIN ].
destruct lfs...
unfold alloc...
rewrite set_neq...
fold (alloc H vs lfs)...
Qed.

Lemma alloc_some :
forall H a ats lfs
  (LEN : length ats = length lfs)
  (IN  : In a ats),
  exists r, alloc H ats lfs a = Some r.
Proof with isa.
induction ats...
contradiction.
unfold alloc in *.
destruct lfs; simpl in *; try discriminate.
unfold set in *.
destruct (eq_nat_dec a a0); subst.
(* eq *)
exists c...
(* neq *)
apply IHats.
inversion LEN...
destruct IN...
destruct n...
Qed.

Definition make_closure (e : env) (g : heap) (p : address)
  (cpvs : vars * code_pointer) : option closure :=
match cpvs with
| (vs, cp) =>
  match map_env e g p vs with
  | Some addrs => Some (cp, addrs)
  | None => None
  end
end.

Fixpoint make_closures (e : env) (g : heap) (p : address)
  (cps : list (vars * code_pointer)) {struct cps} : option closures:=
match cps with
| nil => Some nil
| cp::cps0 =>
  match make_closures e g p cps0 with
  | Some clos =>
    match make_closure e g p cp with
    | Some clo => Some (clo::clos)
    | None => None
    end
  | None => None
  end
end.

Reserved Notation " cs @@ a ^\ b " (at level 70, no associativity).

Inductive Sem (cs : code_store) : (action * stack) -> value -> Prop :=

| Halt : forall Value,
  cs @@ (A Value, nil) ^\ Value

| Cons : forall Gamma C xs sigma addrs cleanup args fake_bot pclo Value K
  (MAPENV  : map_env sigma Gamma pclo xs = Some addrs)
  (ARGSNIL : fake_bot = length args)
  (PREMISE : cs @@ (A (Val_con Gamma C addrs, (skipn cleanup sigma), (args, fake_bot)), K) ^\ Value),
  cs @@ (E (<< Gamma, Constr C xs (cleanup), sigma, (args, fake_bot), pclo >>), K) ^\ Value

| Accum : forall Gamma x xs sigma args p new_args Value cleanup fake_bot pclo K
  (MAPENV  : map_env sigma Gamma pclo xs = Some new_args)
  (LOOKUP  : look_up sigma Gamma pclo x = Some p)
  (PREMISE : cs @@ (E (<< Gamma, p, (new_args++args, fake_bot), skipn cleanup sigma >>), K) ^\ Value),
  cs @@ (E (<< Gamma, App x xs (cleanup), sigma, (args, fake_bot), pclo >>), K) ^\ Value

| App1 : forall cp Gamma p args clovars bind e some_clo sigma fake_bot real_args fake_args Value K
  (CS      : find_cs cs cp = CS_lf (Lf Dont_update clovars bind e))
  (ONHEAP  : Gamma p = Some (cp, some_clo))
  (REAL    : real_args = firstn (length args - fake_bot) args)
  (FAKE    : fake_args = skipn (length args - fake_bot) args)
  (LENGTH  : bind > length args - fake_bot)
  (PREMISE : cs @@ (A (Val_pap Gamma p real_args, sigma, (fake_args, fake_bot)), K) ^\ Value),
  cs @@ (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value 

| App2 : forall cp Gamma p args Value e bind clo clovars sigma fake_bot K
  (CS      : find_cs cs cp = CS_lf (Lf Dont_update clovars bind e))
  (ONHEAP  : Gamma p = Some (cp, clo))
  (LENGTH  : bind <= length args - fake_bot)
  (PREMISE : cs @@ (E (<< Gamma, e, firstn bind args ++ sigma, (skipn bind args, fake_bot), p >>), K) ^\ Value),
  cs @@ (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value

| App_Eval : forall cp Gamma p args Value e clovars clo_e sigma fake_bot K
  (CS      : find_cs cs cp = CS_lf (Lf Update clovars 0 e))
  (ONHEAP1 : Gamma p = Some (cp, clo_e))
  (* NO CLOG !!! *)
  (PREMISE : cs @@ (E (<< Gamma, e, sigma, (args, length args), p >>), K_upd p fake_bot :: K) ^\ Value),
  cs @@ (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value

| App3 : forall p C addrs Delta theta args fake_bot fake_bot_dummy K Value
  (ARGSNIL : fake_bot = length args)
  (PREMISE : cs @@ (A (Val_con (set Delta p (CP_cons C (length addrs), addrs)) C addrs, theta, (args, fake_bot)), K) ^\ Value),
  cs @@ (A (Val_con Delta C addrs, theta, (args, fake_bot)), K_upd p fake_bot_dummy :: K) ^\ Value

| App4 : forall p Value q addrs Delta theta args0 fake_bot fake_bot0 K
  (PREMISE : cs @@ (E (<< set Delta p (CP_pap (length addrs), q :: addrs), q, (addrs++args0, fake_bot), theta >>), K) ^\ Value),
  cs @@ (A (Val_pap Delta q addrs, theta, (args0, fake_bot0)), K_upd p fake_bot :: K) ^\ Value

| Let : forall Gamma e lfs sigma closures Value addrs args pclo K
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) Gamma pclo lfs = Some closures)
  (PREMISE : cs @@ (E (<< alloc Gamma addrs closures, e, addrs++sigma, args, pclo >>), K) ^\ Value),
  cs @@ (E (<< Gamma, Letrec lfs e, sigma, args, pclo >>), K) ^\ Value

| Case_of_Eval : forall Gamma e als sigma pclo Value args fake_bot K
  (PREMISE : cs @@ (E (<< Gamma, e, sigma, (args, length args), pclo >>), K_alt als fake_bot :: K) ^\ Value),
  cs @@ (E (<< Gamma, Case e als, sigma, (args, fake_bot), pclo >>), K) ^\ Value

| Case_of_Apply : forall p_als als pclo Value bind Delta p_e0 e0 C addrs theta args0 fake_bot fake_bot0 K
  (CS1     : find_cs cs p_als = CS_alts als)
  (SELECT  : nth C als = Some (Alt bind p_e0))
  (CS2     : find_cs cs p_e0 = CS_expr e0)
  (PREMISE : cs @@ (E (<< Delta, e0, addrs++theta, (args0, fake_bot), pclo >>), K) ^\ Value),
  cs @@ (A (Val_con Delta C addrs, theta, (args0, fake_bot0)), K_alt p_als fake_bot :: K) ^\ Value

where "cs @@ a ^\ b " := (Sem cs a b).

