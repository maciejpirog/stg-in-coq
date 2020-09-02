Require Import List.
Require Import ListSet.
Require Import Arith.

(** Additional tactics and lemmas. Nothing worth a sligtest
bit of interest. *)

(** * Tactics *)

(** A proud tactic of mine. *)

Ltac isa := intros; simpl in *; auto.

(** * Lists *)

Fixpoint nth {A : Set} (n : nat) (l : list A) {struct n} : option A :=
match n, l with
| O, x :: _ => Some x
| O, _ => None
| S m, nil => None
| S m, x :: t => nth m t
end.

Lemma firstn_app :
forall (T : Type) (xs ys : list T),
  xs = firstn (length xs) (xs ++ ys).
Proof with isa.
intros.
induction xs...
f_equal...
Qed.

Lemma skipn_app :
forall (T : Type) (xs ys : list T),
  ys = skipn (length xs) (xs ++ ys).
Proof with isa.
intros.
induction xs...
Qed.

Lemma firstn_app2 :
forall (T : Type) (n : nat) (xs ys : list T)
  (LEQ : n <= length xs),
  firstn n (xs ++ ys) = firstn n xs.
Proof with isa.
induction n; intros.
inversion LEQ...
destruct xs...
inversion LEQ.
f_equal.
apply le_S_n in LEQ...
Qed.

Lemma skipn_app2 :
forall (T : Type) (n : nat) (xs ys : list T)
  (LEQ : n <= length xs),
  skipn n (xs ++ ys) = skipn n xs ++ ys.
Proof with isa.
induction n; intros.
inversion LEQ...
destruct xs...
inversion LEQ.
apply le_S_n in LEQ...
Qed.

(** * Additional stuff for the [ListSet] library *)

Section set_additional.

Variable A : Type.

Hypothesis Aeq_dec : forall x y:A, {x = y} + {x <> y}.

Definition set_subset (x X : ListSet.set A) : Prop :=
  forall a, set_In a x -> set_In a X.

Lemma set_subset_refl : forall x, set_subset x x.
Proof with isa.
unfold set_subset...
Qed.

Lemma set_subset_union1 : forall x y, set_subset x (set_union Aeq_dec x y).
Proof with isa.
unfold set_subset...
apply set_union_intro1...
Qed.

Lemma set_subset_union2 : forall x y, set_subset y (set_union Aeq_dec x y).
Proof with isa.
unfold set_subset...
apply set_union_intro2...
Qed.

End set_additional.
