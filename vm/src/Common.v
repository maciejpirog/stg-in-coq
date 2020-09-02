Require Import List.
Require Import Arith.

Require Export Utils.

(** * Basic definitions *)

(** Things that are common in most of the intermediate languages
and semantics lay here. *)

(** Each constructor name is a [nat]. It is important since the right
alternative in the semantics of [Case_of] expressions is chosen using
the [nth] function. Thus all "datatypes" (quotes, because the STG language
does not provide explicit datatype declarations) must consist of
constructors being a prefix of a standard order on natural numbers
(0,1,2,3,...), so a list may consist of two constructors: a constant [0]
and a binary [1]. Obviously, constructor names are shared between
datatypes, [1] sometimes means [Cons] and sometimes [True]. *)

Definition constructor := nat.

(** All binders in the STG language are multiple and encoded using
de Bruijn indices. Thus, a binder must state how many variables it binds.
Variables are named left-to right, so a term [\x y z t -> x y z t]
would be encoded as [Abs 3. Application 0 [1,2,3]]. *)

Definition bind := nat.

(** Update flag indicate whether a closure should be updated with
a value after being evaluated. It is not only an optimization, but is
necessary in semantics where lambdas are not first-class. *)

Inductive upd_flag : Set := Update | Dont_update.

Definition upd_flag_eq_dec : forall v w : upd_flag, {v = w} + {v <> w}.
Proof.
decide equality.
Qed.

(** Addresses correspond to physical addresses on the heap. *)

Definition address : Set := nat.

Definition addresses : Set := list address.

(** There are two types of variables. [B_ind] states that the variable
is bound, and the argument of the constructor is its de Bruijn index.
[C_ind] represents "free" variables of the lambda-form, hence "C" for
"closure". The argument states which value from the closure that is
evaluated at the moment is represented. *)

Inductive var : Set :=
| B_ind : nat -> var
| C_ind : nat-> var.

Definition vars := list var.

Definition argstack := addresses.

Definition var_eq_dec : forall v w : var, {v = w} + {v <> w}.
Proof.
decide equality; decide equality.
Qed.

Definition vars_eq_dec : forall vs ws : vars, {vs = ws} + {vs <> ws}.
Proof.
apply list_eq_dec.
apply var_eq_dec.
Qed.

(** * Heaps *)

Definition gen_heap {Clo : Set} : Set := address -> option Clo.

Definition empty_heap {Clo : Set} : gen_heap (Clo := Clo) :=
  fun x => None.

Definition set {Clo : Set} (g : gen_heap) (a : address) (clos : Clo)
  : gen_heap :=
fun (x : address) => if eq_nat_dec x a
  then Some clos
  else g x.

Definition alloc {Clo : Set} (g : gen_heap) (addrs : addresses)
  (clos : list Clo) : gen_heap :=
fold_right (fun (ad : address * Clo) (h : gen_heap) =>
  set h (fst ad) (snd ad))
  g (combine addrs clos).

Definition heap_map {Clo1 : Set} {Clo2 : Set} (f : Clo1 -> Clo2)
  (g : gen_heap) : gen_heap :=
fun (x : address) => match g x with
| None => None
| Some c => Some (f c)
end.

Lemma set_eq :
forall (T : Set) (H : gen_heap (Clo := T)) s v,
  set H s v s = Some v.
Proof with isa.
intros.
unfold set.
destruct (eq_nat_dec)...
tauto.
Qed.

Lemma set_neq :
forall (T : Set) (H : gen_heap (Clo := T)) s v p
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
forall (T : Set) (H : gen_heap (Clo := T)) vs v lfs lf
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
fold (alloc (Clo := T) H vs lfs) in ALLOC.
inversion IN...
contradiction.
Qed.

Lemma alloc_nin :
forall (T : Set) (H : gen_heap (Clo := T)) vs p
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
forall (T : Set) (H : gen_heap (Clo := T)) a ats lfs
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
exists t...
(* neq *)
apply IHats.
inversion LEN...
destruct IN...
destruct n...
Qed.

(** * Environments *)

Definition env : Set := addresses.

(** The [from a b] function creates a list [ [a, a+1, ... a+b] ]. *)

Fixpoint from (a b : nat) {struct b} : list nat :=
match b with
| 0 => nil
| S m => a :: from (S a) m
end.

Lemma from_length :
forall n m, length (from m n) = n.
Proof with isa.
induction n...
Qed.

Definition look_up (e : env) (a : addresses) (v : var) : option address :=
match v with
| B_ind n => nth n e 
| C_ind n => nth n a
end.

Fixpoint map_env (e : env) (a : addresses) (vs : vars) {struct vs}
  : option addresses :=
match vs with
| nil => Some nil
| x::xs =>
  match map_env e a xs with
  | Some ps =>
    match look_up e a x with
    | Some p => Some (p::ps)
    | None => None
    end
  | None => None
  end
end.

(** * Lambda-forms *)

Inductive gen_lambda_form {Expr : Set} : Set :=
| Lf : upd_flag -> vars -> bind -> Expr -> gen_lambda_form.

(** * Alternatives *)

Inductive gen_alt {Expr : Set} : Set :=
| Alt : bind -> Expr -> gen_alt (Expr := Expr).

(** * Closures *)

Inductive node {Expr : Set} : Set :=
| Node : gen_lambda_form (Expr := Expr) -> node
| Black_hole : node.

Definition gen_closure {Expr : Set} : Set :=
(node (Expr := Expr) * addresses)%type.

Definition coer_lf_closure_type {Expr : Set}
  (lf : gen_lambda_form (Expr := Expr)) : node :=
Node lf.

Coercion coer_lf_closure_type : gen_lambda_form >-> node.

Definition Lf_n {Expr : Set} : vars -> bind -> Expr -> node :=
Lf (Expr := Expr) Dont_update.

Definition Lf_u {Expr : Set} : vars -> bind -> Expr -> node :=
Lf (Expr := Expr) Update.

Definition coer_closure_node_closure {Expr : Set}
  (p : gen_lambda_form * list address)
  : gen_closure (Expr := Expr) :=
match p with
| (a , b) => (a : node, b)
end.

Definition gen_closures {Expr : Set} : Set :=
list (gen_closure (Expr := Expr)).

(** * Closures and heaps in cooperation *)

Definition clog {Expr : Set} 
  (g : gen_heap (Clo := gen_closure (Expr := Expr))) (a : address)
  : gen_heap (Clo := gen_closure) :=
fun (x : address) => if eq_nat_dec x a
  then match g x with
    | None => None (* should never happen *)
    | Some (_, addrs) => Some (Black_hole, addrs)
    end
  else g x.

Definition make_closure {Expr : Set} (e : env) (a : addresses)
  (lf : gen_lambda_form (Expr := Expr)) : option gen_closure :=
match lf with
| Lf _ vs _ _ =>
  match map_env e a vs with
  | Some addrs => Some (Node lf, addrs)
  | None => None
  end
end.

Fixpoint make_closures {Expr : Set} (e : env) (a : addresses)
  (lfs : list (gen_lambda_form (Expr := Expr))) {struct lfs}
  : option gen_closures:=
match lfs with
| nil => Some nil
| l::lfs0 =>
  match make_closures e a lfs0 with
  | Some clos =>
    match make_closure e a l with
    | Some clo => Some (clo::clos)
    | None => None
    end
  | None => None
  end
end.

Lemma make_closures_length:
forall T sigma current_clo lfs closures
  (CLOS   : make_closures (Expr := T) sigma current_clo lfs =
    Some closures),
  length lfs = length closures.
Proof with isa.
induction lfs...
destruct closures...
congruence.
destruct closures...
destruct (make_closures sigma current_clo lfs); try discriminate.
destruct (make_closure sigma current_clo a); discriminate.
f_equal.
apply IHlfs.
remember (make_closures sigma current_clo lfs) as mem; destruct mem;
  try discriminate.
remember (make_closure sigma current_clo a) as mem2; destruct mem2;
  try discriminate.
inversion CLOS...
Qed.
