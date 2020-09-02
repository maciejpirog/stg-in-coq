(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains some auxiliary tactics and lemmas, mostly
on lists and nats. *)

Require Import Omega.
Require Export List.
Require Export Max.

(** * Tactics *)

Ltac isa := intros; simpl in *; auto.
Ltac eisa := intros; simpl in *; eauto.

(** The [remember_destruct] tactic destructs a given term, but leaves
its original form as an equality assumption. For example:
[[

a : nat |- P a

Coq < remember_destruct a

(GOAL 1) a : nat, X : 0 = a |- P 0
(GOAL 2) a : nat, H : nat, X : S H = a |- P (S H)
]] *)

Ltac remember_destruct e :=
  let x := fresh "H"
  with y := fresh "H" 
  with z := fresh "X" in
  assert (x : exists p, p = e);
  [ exists e; reflexivity
  | case x; clear x; intro y; intro z; destruct y; try rewrite <- z ].

(** The [dupl] tactic duplicates an assumption. For example:
[[

H : P a |- _

Coq < dupl H

H : P a, H0 : P a |- _
]] *)

Ltac dupl H :=
let ex := fresh "ex"
  with new := fresh H
  with eq := fresh "eq"
  in
  assert (ex : exists x, x = H);
  [ exists H; auto
  | case ex; intros new eq; clear eq]; clear ex.

(** The [dupl_apply] tactic behaves like [apply in], but leaves the
premise untouched and creates additional assumption:
[[

H : A, H1 : A -> B |- _

Coq < dupl_apply H H1

H : A, H1 : A -> B, H2 : B |- _

]]*)

Ltac dupl_apply H HimplY:=
let ex := fresh "ex"
  with new := fresh HimplY
  with eq := fresh "eq"
  in
  assert (ex : exists x, x = H);
  [ exists H; auto
  | case ex; intros new eq; clear eq ];
  eapply HimplY in new; clear HimplY; clear ex.

(** * List *)

(** Strengthening of the standard [map_ext] lemma *)

Lemma map_ext_in :
forall (A B : Type) (f g : A -> B) (l : list A),
  (forall a : A, In a l -> f a = g a) -> map f l = map g l.
Proof with isa.
isa.
induction l...
f_equal...
Qed.

Lemma map_id :
forall (A : Type) (xs : list A), map id xs = xs.
Proof with isa.
isa.
induction xs...
unfold id at 1.
f_equal...
Qed.

Lemma map_neq_nil : forall (A B : Type) (l1 : list A) (l2 : list B)
  (f : A -> B), l2 = map f l1 -> l2 <> nil -> l1 <> nil.
Proof with isa.
intros.
subst.
destruct l1...
auto with *.
Qed.

Lemma in_app_left :
forall (A : Type) (l m : list A) (n : A), In n l -> In n (l ++ m).
Proof with isa.
induction l...
contradiction.
destruct H; subst...
Qed.

Lemma in_app_right :
forall (A : Type) (l m : list A) (n : A), In n m -> In n (l ++ m).
Proof with isa.
induction l...
Qed.

Lemma in_app_comm :
forall (A : Type) (l m : list A) (n : A), In n (m ++ l) -> In n (l ++ m).
Proof with isa.
intros.
apply in_app_or in H.
destruct H; [apply in_app_right | apply in_app_left]...
Qed.

(** The first element of a concatenation is the first element of
the first list or the first list is empty *)
 
Lemma cons_cons_app :
forall (A : Type) (xs ys zs : list A) (x : A),
  x :: xs = ys ++ zs ->
  ys = nil /\ zs = x :: xs \/ exists ks, ys = x :: ks /\ xs = ks ++ zs.
Proof with isa.
intros.
remember_destruct ys...
subst...
right...
exists H0...
subst...
inversion H.
subst...
Qed.

Lemma nil_app :
forall (A : Type) (xs ys: list A),
  nil = xs ++ ys ->
  xs = nil /\ ys = nil.
Proof with isa.
induction xs...
discriminate.
Qed.

Lemma flat_map_is_app :
forall (A B : Type) (xs : list A) (f : A -> list B) (x : A),
  In x xs ->
  exists ys, exists zs,
  flat_map f xs = ys ++ f x ++ zs.
Proof with isa.
intros.
induction xs; inversion H.
(* left *)
subst.
exists nil.
exists (flat_map f xs)...
(* right *)
fold (In x xs) in H0; intuition.
destruct H1.
destruct H1.
exists (f a ++ x0).
exists x1.
rewrite app_ass...
f_equal...
Qed.

(** In the semantics we use a few rules of shape

[[
  P( x_1 x_2 ... x_n )          Q( x_(n+1) ... x_k )
------------------------------------------------------
          R( x_1 x_2 ... x_n x_(n+1) ... x_k )

]]

Such rules are implemented using Coq's standard [firstn] and [skipn],
so the rule would be implemented as:

[[
P (firstn n xs) ->
Q (skipn n xs) ->
R (xs)

]]

We use the following auxiliary lemmas which are not present in
the std library:
*)

Lemma skipn_length_app :
forall (A : Type) (xs ys : list A), skipn (length xs) (xs ++ ys) = ys.
Proof with isa.
induction xs...
Qed.

Lemma firstn_length_app :
forall (A : Type) (xs ys : list A), firstn (length xs) (xs ++ ys) = xs.
Proof with isa.
induction xs...
f_equal...
Qed.

Lemma skipn_app :
forall (A : Type) (pm Ds : list A) (m : nat), m <= length pm ->
  skipn m (pm ++ Ds) = skipn m pm ++ Ds.
Proof with isa.
intros A pm.
induction pm...
inversion H.
isa.
inversion H.
isa.
destruct m...
apply IHpm.
auto with arith.
Qed.

Lemma firstn_app : 
forall (A : Type) (pm Ds : list A) (m : nat), m <= length pm ->
  firstn m (pm ++ Ds) = firstn m pm.
Proof with isa.
intros A pm Ds.
induction pm; isa; inversion H...
f_equal...
destruct m; isa.
f_equal...
auto with arith.
Qed.

Lemma In_skipn :
forall (A : Set) (x : A) (n : nat) (xs : list A),
In x (skipn n xs) -> In x xs.
Proof.
double induction n xs; intuition.
Qed.

Lemma In_firstn :
forall (A : Set) (x : A) (n : nat) (xs : list A),
In x (firstn n xs) -> In x xs.
Proof with isa.
double induction n xs; intuition...
inversion H1.
left...
right...
Qed.

Lemma firstn_length_l:
forall (A : Set) (xs : list A), firstn (length xs) xs = xs.
Proof with isa.
induction xs.
isa.
f_equal...
f_equal...
Qed.

Lemma skipn_length_l:
forall (A : Set) (xs : list A), skipn (length xs) xs = nil.
Proof with isa.
induction xs.
isa.
f_equal...
Qed.

Lemma firstn_length_eq_id :
forall (A : Set) (n : nat) (xs : list A),
  length xs = n -> firstn n xs = xs.
Proof with isa.
induction xs; isa; rewrite <- H...
f_equal.
apply firstn_length_l.
Qed.

Lemma skipn_length_eq_nil :
forall (A : Set) (n : nat) (xs : list A),
  length xs = n -> skipn n xs = nil.
Proof.
induction xs; isa; rewrite <- H; isa.
apply skipn_length_l.
Qed.

Lemma skipn_map :
forall (A B : Set) (n : nat) (xs : list A) (f : A -> B),
  skipn n (map f xs) = map f (skipn n xs).
Proof with isa.
intros A B n.
induction n...
induction xs...
Qed.

Lemma firstn_map :
forall (A B : Set) (n : nat) (xs : list A) (f : A -> B),
  firstn n (map f xs) = map f (firstn n xs).
Proof with isa.
intros A B n.
induction n...
induction xs...
f_equal...
Qed.

Lemma skipn_lt_length_nil :
forall (A : Set) (n : nat) (xs : list A),
  n < length xs -> nil <> skipn n xs.
Proof with isa.
intros A n.
induction n.
intros.
induction xs...
omega.
discriminate...
destruct xs...
omega.
apply IHn.
omega.
Qed.

Lemma firstn_lt_length :
forall (A : Set) (xs : list A) (n : nat),
  n < length xs -> length (firstn n xs) = n.
Proof with isa.
intros A xs.
induction xs...
inversion H.
induction n...
f_equal.
apply IHxs.
omega.
Qed.

Lemma firstn_le_length :
forall (A : Set) (xs : list A) (n : nat),
  n <= length xs -> length (firstn n xs) = n.
Proof with isa.
induction xs...
inversion H...
destruct n...
f_equal...
apply IHxs.
omega.
Qed.

(** * Arithmethics *)

Lemma arith_a_plus_Sb_EQ_Sa_plus_b :
forall a b : nat, a + S b = S a + b.
Proof.
intros; omega.
Qed.

Lemma arith_m_minus_O_EQ_m :
forall m : nat, m - 0 = m.
Proof.
intros.
omega.
Qed.

Lemma n_plus_Sm_minus_1_EQ_n_plus_m:
forall (n m : nat), n + S m - 1 = n + m.
intros.
omega.
Qed.

Lemma n_lt_n_false :
forall (n : nat), ~ n < n.
Proof.
intros.
omega.
Qed.

Lemma arith_n_depends_on_m :
forall (n m : nat), exists a : nat, exists b : nat, n = a + m - b.
Proof.
intros.
exists n; exists m.
omega.
Qed.

Lemma arith_another_S_minus_1 :
forall (x x0 m : nat), x + S m - x0 - 1 = x + m - x0.
Proof.
intros.
omega.
Qed.

Lemma arith_a_plus_b_minus_c_minus_b :
forall (a b c : nat), a + b - c - b = a - c.
intros.
omega.
Qed.

Ltac simpl_arith := repeat
(
  try rewrite <- plus_n_O in * |- *;
  try rewrite arith_another_S_minus_1 in * |- *;
  try rewrite n_plus_Sm_minus_1_EQ_n_plus_m  in * |- *;
  try rewrite arith_a_plus_b_minus_c_minus_b  in * |- *
).

Lemma max_c_inv_to_le :
forall c b a, a <= b -> max a c <= max b c.
Proof.
induction c; induction a; induction b; isa; intuition.
Qed.

