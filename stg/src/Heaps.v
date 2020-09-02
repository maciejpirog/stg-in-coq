(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains definitions used in semantics: selecting an
alternative in a case expression and two types of heaps.

[heapA] is used in semantics with substitutions, hence the type
[var -> option lambda_form].

[heapB] is used in semantics with environments, hence the type
[var -> option (lambda_form * env)]. *)

Require Export Subst.

(** * Lambda forms *)

Definition Lf_n := Lf Dont_update.

Definition Lf_u := Lf Update 0.

(** * Cases *)

Fixpoint select_case (als : alts) (c : constructor) {struct als} :
  option alt :=
match als with
| ((Alt c0 b e) as al) :: als0 => if eq_nat_dec c c0
    then Some al
    else select_case als0 c
| nil => None
end.

Lemma select_case_name :
forall als c c0 m e,
  select_case als c = Some (Alt c0 m e) -> c = c0.
Proof with isa; intuition.
intuition.
induction als...
discriminate.
destruct a.
destruct eq_nat_dec...
inversion H; subst...
Qed.

Lemma In_select_case :
forall als c c0 m e,
  select_case als c = Some (Alt c0 m e) ->
  In (Alt c0 m e) als.
Proof with isa; intuition.
intros.
induction als...
discriminate.
destruct a.
destruct eq_nat_dec.
(* = *)
subst.
inversion H; subst...
(* <> *)
right...
Qed.

(** * HeapA *)

Definition heapA := var -> option lambda_form.

Definition emptyA := fun _ : var => None (A := lambda_form).

Definition setA (g : heapA) (a : var) (lf : lambda_form) : heapA :=
fun (x : var) => if eq_var_dec x a
  then Some lf
  else g x.

Definition allocA (g : heapA) (ats : vars) (lfs : defs) : heapA :=
fold_right (fun (ad : var * lambda_form) (h : heapA) =>
  setA h (fst ad) (snd ad))
  g (combine ats lfs).

Theorem setA_eq : forall H s v, setA H s v s = Some v.
Proof with intuition.
intros.
unfold setA.
destruct eq_var_dec...
Qed.

Theorem setA_neq : forall H s v p, p <> s -> setA H p v s = H s.
Proof with intuition.
intros.
unfold setA.
destruct eq_var_dec...
symmetry in e.
intuition.
Qed.

Theorem allocA_in :
forall (H : heapA) (vs : vars) (v : var) (lfs : defs) (lf : lambda_form),
  length vs = length lfs -> In v vs ->
  allocA H vs lfs v = Some lf -> In lf lfs.
Proof with eisa.
intros H vs.
induction vs...
contradiction.
destruct lfs.
simpl in *.
discriminate H0.
destruct (eq_var_dec a v).
unfold allocA in H2.
simpl in *.
subst.
rewrite setA_eq in H2.
left.
inversion H2.
auto.
inversion H1...
intuition.
right.
eapply IHvs...
inversion H0...
unfold allocA in H2.
simpl in H2.
rewrite setA_neq in H2...
Qed.

Theorem allocA_nin :
forall (H : heapA) (vs : vars) (p : var) (lfs : defs),
  ~ In p vs -> allocA H vs lfs p = H p.
Proof with intuition.
assert (forall (H : heapA) (vs : vars) (p : var),
    ~ In p vs -> forall (lfs : defs), allocA H vs lfs p = H p).
  intros Heap vs p H0.
  induction vs.
  intuition.
  assert (NOTIN : forall A p (x : A) xs,
    ~ In p (x :: xs) -> p <> x /\ ~ In p xs).
    clear.
    isa.
  apply NOTIN in H0.
  destruct H0.
  clear NOTIN.
  destruct lfs...
  unfold allocA.
  simpl.
  rewrite setA_neq...
  fold (allocA Heap vs lfs)...
intuition.
Qed.

Lemma allocA_some :
forall a ats H lfs,
  length ats = length lfs ->
  In a ats ->
  exists r, allocA H ats lfs a = Some r.
Proof with isa.
induction ats...
contradiction.
unfold allocA in *.
destruct lfs; simpl in *; try discriminate.
unfold setA in *.
destruct (eq_var_dec a a0).
(* eq *)
exists l.
trivial.
(* neq *)
apply IHats.
inversion H0...
destruct H1...
destruct n...
Qed.

(** * HeapB *)

Definition heapB := nat -> option (lambda_form * env).

Definition emptyB := fun _ : nat => None (A := lambda_form * env).

Definition setB (g : heapB) (n : nat) (lfe : lambda_form * env) : heapB :=
fun (x : nat) => if eq_nat_dec x n
  then Some lfe
  else g x.

Definition allocB (g : heapB) (ns : list nat)
  (lfes : list (lambda_form * env)) : heapB :=
fold_right (fun (ade : nat * (lambda_form * env)) (h : heapB) =>
  setB h (fst ade) (snd ade))
  g (combine ns lfes).

Theorem setB_eq : forall H s v, setB H s v s = Some v.
Proof with intuition.
intros.
unfold setB.
destruct eq_nat_dec...
Qed.

Theorem setB_neq : forall H s v p, p <> s -> setB H p v s = H s.
Proof with intuition.
intros.
unfold setB.
destruct eq_nat_dec...
symmetry in e.
intuition.
Qed.

Theorem allocB_in :
forall (H : heapB) (vs : list nat) (v : nat)
  (lfs : list (lambda_form * env)) (lf : lambda_form * env),
  length vs = length lfs -> In v vs ->
  allocB H vs lfs v = Some lf -> In lf lfs.
Proof with isa.
intros H vs.
induction vs...
contradiction.
destruct lfs.
simpl in *.
discriminate H0.
destruct (eq_nat_dec a v).
unfold allocB in H2.
simpl in *.
subst.
rewrite setB_eq in H2.
left.
inversion H2.
auto.
inversion H1.
intuition.
simpl.
right.
eapply IHvs.
simpl in H0.
inversion H0...
apply H3.
unfold allocB in H2.
simpl in H2.
rewrite setB_neq in H2...
Qed.

Theorem allocB_nin :
forall (H : heapB) (vs : list nat) (p : nat)
  (lfs : list (lambda_form * env)),
  ~ In p vs -> allocB H vs lfs p = H p.
Proof with intuition.
assert (forall (H : heapB) (vs : list nat) (p : nat),
    ~ In p vs -> forall (lfs : list (lambda_form * env)),
    allocB H vs lfs p = H p).
  intros Heap vs p H0.
  induction vs...
  assert (NOTIN : forall A p (x : A) xs,
      ~ In p (x :: xs) -> p <> x /\ ~ In p xs).
    isa.
  apply NOTIN in H0.
  destruct H0.
  clear NOTIN.
  destruct lfs...
  unfold allocB.
  simpl.
  rewrite setB_neq...
  fold (allocB Heap vs lfs)...
intuition.
Qed.

Lemma allocB_some :
forall a ats H lfs,
  length ats = length lfs ->
  In a ats ->
  exists r, allocB H ats lfs a = Some r.
Proof with isa.
induction ats...
contradiction.
unfold allocB in *.
destruct lfs; simpl in *; try discriminate.
unfold setB in *.
destruct (eq_nat_dec a a0).
(* eq *)
exists p.
trivial.
(* neq *)
apply IHats.
inversion H0...
destruct H1...
destruct n...
Qed.

(** * Similarity *)

Definition similar (ha : heapA) (hb : heapB) : Prop :=
(forall (n : nat), ha (Index n) = None) /\
(forall (a : atom), ha (Atom a) = None <-> hb a = None) /\
(forall a pi0 pi1 b0 b1 etau e tau,
  ha (Atom a) = Some (Lf pi0 b0 etau) ->
  hb a = Some (Lf pi1 b1 e, tau) ->
  pi0 = pi1 /\ b0 = b1 /\ etau = e~[shift b1 tau]).

Lemma similar_empty :
similar emptyA emptyB.
Proof with isa.
unfold emptyA.
unfold emptyB.
unfold similar.
intuition; discriminate.
Qed.

Lemma similar_dom_atom :
forall Gamma GammaP lf p,
  similar Gamma GammaP ->
  Gamma p = Some lf -> is_atom p.
Proof.
intros.
inversion H.
destruct p.
rewrite H1 in H0.
discriminate.
constructor.
Qed.

Lemma similar_value_right :
forall Gamma GammaP a b m etau,
  Gamma (Atom a) = Some (Lf b m etau) ->
  similar Gamma GammaP ->
  exists e, exists tau, GammaP a = Some (Lf b m e, tau)
  /\ etau = e~[shift m tau].
Proof.
intros.
inversion H0.
inversion H2.
assert (exists k, GammaP a = k).
  exists (GammaP a).
  auto.
destruct H5.
destruct x.
destruct p.
destruct l.
exists e0.
exists e.
assert (b = u /\ m = b0 /\ etau = e0~[shift b0 e]).
  apply H4 with (a := a).
  auto.
auto.
destruct H6.
destruct H7.
subst.
split.
apply H5.
auto.
destruct H2.
destruct H2 with (a := a).
rewrite H in H8.
apply H8 in H5.
discriminate H5.
Qed.

Lemma similar_value_left :
forall (Gamma : heapA) (GammaP : heapB) a b m e tau,
  GammaP a = Some (Lf b m e, tau) ->
  similar Gamma GammaP ->
  Gamma (Atom a) = Some (Lf b m (e~[shift m tau])).
Proof with isa.
isa.
destruct H0.
destruct H1.
remember (Gamma (Atom a)) as g.
destruct g.
destruct l.
ecase H2; eauto...
subst.
destruct H4.
f_equal...
f_equal...
intuition.
case H1 with (a := a)...
symmetry in Heqg.
apply H3 in Heqg.
rewrite H in Heqg.
discriminate.
Qed.

(** Whenever a [heapA] Gamma is similar to a [heapB] GammaP,
the [similar_value] tactic splits any value of the former into
an expression and a substitution in the latter. For example:

[[
H : Gamma (Atom a) = Some (Lf_n m e),
H1 : similar Gamma GammaP |- _

Coq < similar_value H GammaP

x0 : expr,
x1 : env,
H : GammaP a = Some (Lf_n m x0, x1),
H2 : e = x0 ~ [shift m x1],
H1 : similar Gamma GammaP |- _
]]
*)

Ltac similar_value H X :=
apply similar_value_right with (GammaP := X) in H; [ | isa ];
  do 3 destruct H.
