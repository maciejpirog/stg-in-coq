Require Import List.

Inductive box (A : Set) : Set :=
| Box : A -> box A.

Inductive r : Set :=
| B : r
| R : list (box r) -> r.

Theorem r_rec2 :
forall (P : r -> Prop),
  P B -> 
  (forall bs, (forall (b : box r), In b bs ->
    match b with Box s => P s end) -> P (R bs)) ->
  forall (a : r), P a.
Proof.
intros ? ? ?.
refine (fix rec (a : r) : P a := _).
destruct a.
(* Case B *)
apply H.
(* Case R *)
apply H0.
induction l.
intros; inversion H1.
intros.
simpl in H1.
inversion H1.
rewrite <- H2.
destruct a.
apply rec.
apply IHl.
apply H2.
Qed.