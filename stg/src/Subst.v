(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains definitions, operations and properties
of substitutions and environments.

Environment is an association list of type [(nat * var)]. In all of the
semantic predicates we substitute only variables (hence [var] as
the second element of the product) for bound variables (represented as
[Indices], thus the type [nat] for keys).

Substitution is a function of type [var -> var]. The environment can be
transformed into substitution using the [subst_var] function.
The substitution is then performed over a term, using the [Lang.map_expr]
function (see the definition of [subst]). *)

Require Export Lang.

(** * Environments *)

Definition env : Set := list (nat * var).

Definition prod_nat_var_dec : forall (p s : nat * var),
  {p = s} + {p <> s}.
Proof.
intros.
repeat decide equality.
Qed.

(** * Assoc lists *)

Fixpoint find_assoc (nas : env) (m : nat) {struct nas} :
  option var :=
match nas with
| (n, a) :: s => if eq_nat_dec m n
    then Some a
    else find_assoc s m
| nil => None
end.

Definition assoc_keys (xs : env) : list nat :=
map (fst (A := nat) (B := var)) xs.

Theorem find_assoc_garbage :
forall (xs ys : env) (a : var) (n n0 : nat), n <> n0 ->
  find_assoc (xs ++ (n, a) :: ys) n0 = find_assoc (xs ++ ys) n0.
Proof with isa.
intros.
induction xs...
destruct eq_nat_dec...
destruct H...
destruct a0.
destruct eq_nat_dec...
Qed.

Theorem find_assoc_in :
forall (nas : env) (n : nat) (a : var),
  find_assoc nas n = Some a -> In (n, a) nas.
Proof with isa.
intros; induction nas...
discriminate.
destruct a0.
destruct eq_nat_dec; subst...
inversion H; subst...
Qed.

Theorem assoc_keys_ex_value :
forall (xs : env) (n : nat),
  In n (assoc_keys xs) -> exists a : var, In (n, a) xs.
Proof with isa.
intros.
induction xs...
contradiction.
inversion_clear H.
exists (snd a).
left; destruct a; simpl in *; subst; auto.
case IHxs; auto; intros; exists x; auto.
Qed.

Theorem assoc_value_ex_key :
forall (xs : env) (n : nat) (a : var),
  In (n, a) xs -> In n (assoc_keys xs).
Proof with isa.
intros.
induction xs...
inversion H; isa.
rewrite H0...
Qed.

Theorem assoc_keys_perm :
forall (xs ys : env), Permutation xs ys ->
  Permutation (assoc_keys xs) (assoc_keys ys).
Proof.
apply Permutation_map.
Qed.

Theorem assoc_keys_perm_in :
forall (xs ys : env) (n : nat), Permutation xs ys ->
  In n (assoc_keys xs) -> In n (assoc_keys ys).
Proof.
intros.
eapply Permutation_map in H.
eapply Permutation_in; [ apply H | auto ].
Qed.

Theorem find_assoc_notin :
forall (xs : env) (n : nat),
  ~ In n (assoc_keys xs) -> find_assoc xs n = None.
Proof with isa.
intros.
induction xs...
destruct a.
destruct eq_nat_dec; subst.
destruct H; left; auto.
case (In_dec eq_nat_dec n (assoc_keys xs)); isa.
Qed.

Lemma find_assoc_in_keys_ex_value :
forall (nas : env) (n : nat),
  In n (assoc_keys nas) ->
  exists s, find_assoc nas n = Some s.
Proof with isa.
intros.
induction nas; isa; try contradiction.
destruct (eq_nat_dec (fst a) n).
(* eq *)
destruct a.
exists v.
destruct eq_nat_dec...
subst; destruct n1...
(* neq *)
destruct H.
  (* left *)
destruct n0...
  (* right *)
destruct a.
destruct eq_nat_dec...
exists v...
Qed.

Lemma assoc_keys_app_distr :
forall mu nu,
  assoc_keys (mu ++ nu) = assoc_keys mu ++ assoc_keys nu.
Proof with isa.
intros.
induction mu...
f_equal...
Qed.

(** * Creating assoc list from list of vars *)

(** The [zip_var_list] function takes a list of variables and a number,
and makes an environment with keys descending, starting from the
predecessor of that number, for example:

[zip_var_list 6 [Index 2, Atom 5, Index 7] = [(5, Index 2),
(4, Atom 5), (3, Index 7)]]
*)

Fixpoint zip_var_list (n : nat) (ats : list var) {struct ats}
  : (env) :=
match ats with
| a :: ts => (n - 1, a) :: zip_var_list (n - 1) ts
| nil => nil
end.

Theorem zip_var_list_length_plus_n_gt :
forall (ats : list var) (n m : nat),
  In m (assoc_keys (zip_var_list (length ats + n) ats)) ->
  m < (length ats + n).
Proof with isa.
intros.
induction ats...
contradiction.
destruct H.
omega.
assert (m < length ats + n).
  apply IHats.
  rewrite arith_m_minus_O_EQ_m in H.
  auto.
omega.
Qed.

Theorem zip_var_list_gt :
forall (ats : list var) (n m : nat), n >= length ats -> 
  In m (assoc_keys (zip_var_list n ats)) -> m < n.
Proof with isa.
intros.
assert (H1 : exists n0, n = length ats + n0).
  exists (n - length ats).
  omega.
case H1...
rewrite H2 in H0 |- *.
apply zip_var_list_length_plus_n_gt; isa.
Qed.

Theorem zip_var_list_domain :
forall (ats : list var) (n m : nat), m < n -> m >= n - length ats -> 
  In m (assoc_keys (zip_var_list n ats)).
Proof with isa.
intros.
assert (exists n0, exists n1, n = n0 + length ats - n1).
  apply arith_n_depends_on_m.
case H1; isa.
case H2; isa.
rewrite H3 in *.
clear H3 n.
induction ats...
omega.
case (eq_nat_dec (x + S (length ats) - x0 - 1) m); isa.
right.
assert (arith : x + S (length ats) - x0 - 1 = x + length ats - x0).
  apply arith_another_S_minus_1.
rewrite arith in *.
apply IHats.
simpl_arith.
clear H1 H2 IHats arith.
omega.
simpl_arith.
omega.
exists x; exists x0; auto.
exists x0; auto.
Qed.

Theorem zip_var_list_domain2 :
forall (ats : list var) (n m : nat),
  In m (assoc_keys (zip_var_list n ats)) ->
  m <= (n - 1) /\ m >= n - length ats.
Proof with isa.
intros.
assert (exists n0, exists n1, n = n0 + length ats - n1).
  apply arith_n_depends_on_m.
case H0; isa.
case H1; isa.
clear H0; clear H1.
subst.
induction ats; isa; simpl_arith; intuition.
Qed.

Lemma In_zip_var_list:
forall a pm n m,
  In (n, a) (zip_var_list m pm) -> In a pm.
Proof with isa.
induction pm...
destruct (eq_var_dec a0 a)...
right.
destruct H.
inversion H; subst.
destruct n0...
apply IHpm with (m := m - 1) (n := n)...
Qed.

(** * Substituting for variables *)

(** The function [subst_var] maps an environment over a variable.
If the variable is an atom or is not in the domain of the environment,
the function leaves the variable untouched. *)

Definition subst_var (nas : env) (v : var) : var :=
match v with
| Index k =>
  match find_assoc nas k with
  | Some a => a
  | None => v
  end
| Atom a => v
end.

Lemma subst_var_atom :
forall f a, subst_var f (Atom a) = Atom a.
Proof.
intros.
unfold subst_var.
trivial.
Qed.

(** * Shifting, trimming and other operations on environments *)

(** The [shift] operation adds an offset to the domain of
an environment, for example:
[[

shift 3 [(1, Index 3), (7, Index 4)] = [(4, Index 3), (10, Index 4)]
]] *)

Definition shift_assoc (offset : nat) (na : nat * var) : nat * var :=
match na with
| (n, a) => (n + offset, a)
end.

Definition shift (offset : nat) (xs : env) : env :=
map (shift_assoc offset) xs.

(** The [env_find] function finds a value for a key (a variable) in
an environment. If the key is an atom, the function fails. *)

Definition env_find (e : env) (v : var) : option var := 
match v with
| Atom _ => None
| Index n => find_assoc e n
end.

(** The [trim] operation trims the domain of an environment to a
specified list of variables (atoms on the list are obviously ignored).
[[


]] *)

Definition trim (nas : env) (vs : vars) : env :=
filter (fun (x : nat * var) =>
  match x with
  | (n, a) => if In_dec eq_var_dec (Index n) vs then true else false
  end) nas.

(** [env_map] maps an environment over a list of variables.
The function fails if there is a variable on the list which is an atom or
is not in the domain of the environment.
[[

env_map [(1, Index 3), (7, Index 4), (5, Atom 4)] [Index 1, Index 5] = [Index 3, Atom 4]
env_map [(1, Index 3), (7, Index 4), (5, Atom 4)] [Atom 1, Index 5] = None
env_map [(1, Index 3), (7, Index 4), (5, Atom 4)] [Index 2, Index 5] = None
]] *)

Fixpoint env_map (e : env) (vs : vars) {struct vs} : option vars :=
match vs with
| nil => Some nil
| (Index m) :: ms =>
  match env_map e ms with
  | None => None
  | Some ks => 
    match find_assoc e m with
    | None => None
    | Some v => Some (v :: ks)
    end
  end
| (Atom _) :: _ => None
end.

Lemma subst_var_env_find :
forall x beta a,
  no_atoms_var x ->
  Atom a = subst_var beta x ->
  env_find beta x = Some (Atom a).
Proof with isa.
isa.
unfold env_find.
unfold subst_var in H0.
destruct x; [ | inversion H ].
destruct find_assoc.
subst...
discriminate.
Qed.

Lemma env_find_subst_var :
forall sigma x p,
  env_find sigma x = Some (Atom p) -> 
  subst_var sigma x = Atom p.
Proof.
intros.
unfold subst_var.
unfold env_find in *.
destruct x.
rewrite H.
trivial.
discriminate.
Qed.

Lemma env_map_map_subst :
forall (beta : env) (xs : vars),
  no_atoms_vars xs ->
  closed_by_vars (assoc_keys beta) 0 xs ->
  env_map beta xs = Some (map (subst_var beta) xs).
Proof with isa.
induction xs...
destruct a...
(* Index *)
rewrite IHxs...
  (* thesis *)
inversion H0.
assert (In (Index n) (Index n :: xs)); auto with *.
apply H1 in H2.
inversion_clear H2.
  (* case 1 *)
apply find_assoc_in_keys_ex_value in H3.
destruct H3.
rewrite <- plus_n_O.
rewrite H2...
  (* case 2 *)
inversion H3.
(* premises of IHxs *)
    (* no_atoms_vars *)
constructor...
inversion_clear H.
apply H2...
    (* closed_by_vars *)
constructor...
inversion_clear H0.
apply H2...
(* Atom *)
inversion_clear H.
assert (In (Atom a) (Atom a :: xs)); auto with *.
apply H1 in H.
inversion H.
Qed.

Lemma map_subst_env_map :
forall sigma xm sigma_xm,
  env_map sigma xm = Some sigma_xm ->
  map (subst_var sigma) xm = sigma_xm.
Proof with isa.
induction xm...
inversion H...
destruct sigma_xm.
(* nil *)
destruct a...
destruct env_map...
destruct find_assoc...
inversion H.
discriminate.
discriminate.
discriminate.
(* cons *)
destruct a.
unfold subst_var.
destruct env_map.
destruct find_assoc.
inversion H; subst...
f_equal.
rewrite <- IHxm...
discriminate.
discriminate.
discriminate.
Qed.

Lemma shift_0_v :
forall tau, shift 0 tau = tau.
Proof with isa.
induction tau...
f_equal...
destruct a...
f_equal...
Qed.

Lemma In_shift :
forall m n a tau,
  In (n, a) (shift m tau) -> In (n - m, a) tau.
Proof with auto with arith; isa.
intros.
unfold shift in H.
apply in_map_iff in H.
destruct H.
destruct H.
destruct x.
unfold shift_assoc in H.
inversion H.
subst.
assert (n0 + m - m = n0).
  omega.
rewrite H1...
Qed.

Lemma shift_in :
forall m k x mu,
  In (m, x) mu -> In (m + k, x) (shift k mu).
Proof with isa.
induction mu...
destruct H; subst...
Qed.

Lemma shift_lt_subst_var_id :
forall n m tau,
  n < m ->
  subst_var (shift m tau) (Index n) = Index n.
Proof with isa.
intros.
unfold subst_var.
cutrewrite (find_assoc (shift m tau) n = None)...
induction tau...
destruct a...
destruct eq_nat_dec...
cut (n < n)...
apply n_lt_n_false in H0.
contradiction.
omega.
Qed.

Lemma find_assoc_shift_lt :
forall n m tau,
  n < m ->
  find_assoc (shift m tau) n = None.
Proof with isa.
induction tau...
destruct a...
destruct eq_nat_dec...
rewrite e in H.
assert (m < m).
  omega.
apply n_lt_n_false in H0.
contradiction.
Qed.

Lemma subst_var_app_shift_lt :
forall m n pn tau,
  n < m ->
  subst_var (zip_var_list m pn ++ shift m tau) (Index n) =
  subst_var (zip_var_list m pn) (Index n).
Proof with isa.
intros.
unfold subst_var.
induction (zip_var_list m pn)...
rewrite find_assoc_shift_lt...
destruct a.
destruct eq_nat_dec...
Qed.

Lemma subst_var_app_shift_ge :
forall n pn m tau r,
  m <= n ->
  m >= length pn ->
  r <= m ->
  subst_var (zip_var_list r pn ++ shift m tau) (Index n) =
  subst_var (shift m tau) (Index n).
Proof with isa.
intros.
assert (m = length pn + (m - length pn)).
  omega.
remember (m - length pn) as k.
clear Heqk H0.
revert k H2.
revert r H1.
induction pn...
destruct eq_nat_dec.
(* eq *)
rewrite e in H.
assert (m < m).
  omega.
apply n_lt_n_false in H0.
contradiction.
(* neq *)
apply IHpn with (k := S k); omega.
Qed.

Lemma shift_app_distr :
forall m sigma tau,
  shift m (sigma ++ tau) = shift m sigma ++ shift m tau.
Proof with isa.
induction sigma...
f_equal...
Qed.

Lemma shift_cummulative :
forall m n tau,
  shift m (shift n tau) = shift (m + n) tau.
Proof with isa.
induction tau...
f_equal...
destruct a...
f_equal.
omega.
Qed.

Lemma shift_zip_var_list :
forall m b qs,
  b >= length qs ->
  shift m (zip_var_list b qs) = zip_var_list (b + m) qs.
Proof with isa.
intros.
assert (b = length qs + (b - length qs)).
  omega.
remember (b - length qs) as k.
clear H Heqk.
revert m b k H0.
induction qs...
f_equal.
f_equal.
omega.
cutrewrite (b + m - 1 = (b - 1) + m).
apply IHqs with (k := k); omega...
omega.
Qed.

Lemma find_assoc_shift :
forall n m beta,
  n >= m ->
  find_assoc beta (n - m) = find_assoc (shift m beta) n.
Proof with isa.
intros.
induction beta...
destruct a.
destruct eq_nat_dec...
destruct eq_nat_dec...
subst.
assert (n <> n).
  omega.
case H0; auto.
destruct eq_nat_dec...
subst.
assert (n0 <> n0).
  omega.
case H0; auto.
Qed.

(** * Substitutions *)

Definition subst (xs : env) (e : expr) : expr :=
map_expr (subst_var xs) 0 e.

Notation " e ~ [ xs ] " := (subst xs e) (at level 40).

Definition subst_lf (xs : env) (lf : lambda_form) : lambda_form :=
map_lf (subst_var xs) 0 lf.

Notation " lf ~~ [ xs ] " := (subst_lf xs lf) (at level 40).

(** * Properities of substitutions *)

Lemma atoms_closed_app :
forall p ps, closed_expr 0 (App p ps) -> is_atom p /\ are_atoms ps.
Proof with intuition.
intros.
inversion H; subst.
split; [ clear H3 | clear H2 ].
inversion H2; subst.
inversion H2...
inversion H0.
unfold is_atom...
inversion H3.
unfold are_atoms.
intros.
case H0 with (v := a)...
inversion H2.
unfold is_atom...
Qed.

Lemma closed_rem_args :
forall p ps, closed_expr 0 (App p ps) -> closed_expr 0 (App p nil).
Proof with isa.
intros.
inversion H; subst; constructor...
constructor; isa; try contradiction.
Qed.

Lemma closed_0_args :
forall p ps, closed_expr 0 (App p ps) -> are_atoms ps.
Proof.
isa.
apply atoms_closed_app in H.
intuition.
Qed.

Lemma open_inv_to_closed_var :
forall ats b v,
  are_atoms ats ->
  closed_by_var nil (length ats + b) v ->
  closed_by_var nil b
    (apply_with_offset (subst_var (zip_var_list (length ats) ats)) b v).
Proof with isa.
isa.
destruct v...
(* Case index *)
inversion_clear H0.
  (* env *)
inversion H1.
  (* index *)
destruct le_lt_dec.
    (* b <= n *)
induction ats...
      (* nil *)
assert (b < b).
  omega.
assert (~ b < b).
  omega.
tauto.
      (* cons *)
destruct eq_nat_dec.
        (* eq *)
apply atoms_head in H.
to_atom a.
apply closed_by_var_atom.
        (* neq *)
rewrite arith_m_minus_O_EQ_m in *.
apply atoms_tail in H.
apply IHats...
omega.
    (* n < b *)
apply closed_by_var_index...
(* Case atom *)
apply closed_by_var_atom.
Qed.

Lemma open_inv_to_closed_vars :
forall ats b vs,
  are_atoms ats ->
  closed_by_vars nil (length ats + b) vs ->
  closed_by_vars nil b
    (map (apply_with_offset (subst_var (zip_var_list (length ats) ats))
    b) vs).
Proof with isa.
isa.
constructor...
apply in_map_iff in H1.
destruct H1.
destruct H1.
subst.
apply open_inv_to_closed_var...
inversion_clear H0.
apply H1...
Qed.

Lemma open_inv_to_closed2 :
forall ats b e0,
  are_atoms ats ->
  closed_by_expr nil (length ats + b) e0 ->
  closed_by_expr nil b
    (map_expr (subst_var (zip_var_list (length ats) ats)) b e0).
Proof with isa.
isa.
revert b H0.
induction e0 using expr_ind2 with
    (P1 := fun (lf : lambda_form) => forall b,
      closed_by_lf nil (length ats + b) lf ->
      closed_by_lf nil b
        (map_lf (subst_var (zip_var_list (length ats) ats)) b lf))
    (P2 := fun (al : alt) => forall b,
      closed_by_alt nil (length ats + b) al ->
      closed_by_alt nil b
        (map_alt (subst_var (zip_var_list (length ats) ats)) b al))...
(* Case App *)
inversion_clear H0.
constructor.
apply open_inv_to_closed_var...
apply open_inv_to_closed_vars...
(* Case Constr *)
inversion_clear H0.
constructor.
apply open_inv_to_closed_vars...
(* Case Letrec *)
constructor...
  (* defs *)
rewrite map_length.
apply in_map_iff in H2.
destruct H2.
destruct H2.
rewrite <- H2.
inversion_clear H1.
apply H0...
rewrite plus_assoc.
apply H4...
  (* expr *)
rewrite map_length.
apply IHe0.
inversion_clear H1.
rewrite plus_assoc...
(* Case Case *)
constructor...
  (* expr *)
apply IHe0.
inversion_clear H1...
  (* alts *)
apply in_map_iff in H2.
destruct H2.
destruct H2.
rewrite <- H2.
inversion_clear H1.
apply H0...
(* Case Lf *)
inversion_clear H0.
constructor.
apply IHe0...
rewrite plus_assoc...
(* Case Alt *)
inversion_clear H0.
constructor.
apply IHe0...
rewrite plus_assoc...
Qed.

Lemma split_atom_find_assoc :
forall ats n b,
  b <= n ->
  find_assoc (zip_var_list (length ats) ats) (n - b) =
  find_assoc (zip_var_list (length ats + b) ats) n.
Proof with isa.
isa.
induction ats...
destruct eq_nat_dec...
destruct eq_nat_dec...
assert (K : n = length ats + b).
  omega.
rewrite K in n0.
rewrite arith_m_minus_O_EQ_m in *.
tauto.
rewrite arith_m_minus_O_EQ_m in *.
rewrite arith_m_minus_O_EQ_m in *.
destruct eq_nat_dec...
rewrite e in n0.
assert (K0 : length ats <> length ats).
  omega.
tauto.
Qed.

Lemma split_atom_find_assoc0 :
forall b c n ats,
  b + c <= n ->
  find_assoc (zip_var_list (length ats) ats) (n - (b + c)) =
  find_assoc (zip_var_list (length ats + b) ats) (n - c).
Proof with isa.
isa.
induction ats...
destruct eq_nat_dec...
(* n - (b + c) = length ats *)
destruct eq_nat_dec...
assert (1 = 0).
  omega.
discriminate.
(* n - (b + c) = length ats *)
destruct eq_nat_dec...
assert (1 = 0).
  omega.
discriminate.
rewrite arith_m_minus_O_EQ_m in *.
rewrite arith_m_minus_O_EQ_m in *.
trivial.
Qed.

Lemma split_atom_apply_with_offset :
forall ats b c v,
  are_atoms ats ->
  apply_with_offset (subst_var (zip_var_list (length ats) ats))
    (b + c) v =
  apply_with_offset (subst_var (zip_var_list (length ats + b) ats)) c v.
Proof with isa.
intros.
destruct v...
destruct le_lt_dec...
(* b + c <= n *)
destruct le_lt_dec...
  (* c <= n *)
rewrite split_atom_find_assoc0...
unfold plus_offset.
induction ats; isa; [ auto with * | ]...
apply atoms_cons in H.
destruct a.
destruct H.
inversion H0.
destruct eq_nat_dec...
rewrite arith_m_minus_O_EQ_m in *.
tauto.
  (* n < c *)
induction ats; isa; auto with *...
destruct eq_nat_dec...
rewrite arith_m_minus_O_EQ_m in *.
apply le_lt_trans with (n := b + c) in l0...
assert (c < c).
  omega.
assert (~ c < c).
  omega.
tauto.
rewrite arith_m_minus_O_EQ_m in *.
apply IHats.
apply atoms_cons in H.
tauto.
(* n < b + c *)
destruct le_lt_dec...
induction ats; isa; auto with *...
destruct eq_nat_dec...
rewrite arith_m_minus_O_EQ_m in *.
assert (n = length ats + b - c).
  omega.
rewrite H0 in l0.
assert (length ats + b < b).
  omega.
assert (b < b).
  omega.
assert (~ b < b).
  omega.
tauto.
rewrite arith_m_minus_O_EQ_m in *.
apply IHats.
apply atoms_cons in H.
tauto.
Qed.

Hint Resolve split_atom_apply_with_offset.

Lemma split_atom_map_offset0 :
forall e b c ats,
  are_atoms ats ->
  map_expr (subst_var (zip_var_list (length ats) ats)) (b + c) e =
  map_expr (subst_var (zip_var_list (length ats + b) ats)) c e.
Proof with isa.
induction e using expr_ind2 with
    (P1 := fun (lf : lambda_form) => forall b c ats,
      are_atoms ats ->
      map_lf (subst_var (zip_var_list (length ats) ats)) (b + c) lf =
      map_lf (subst_var (zip_var_list (length ats + b) ats)) c lf)
    (P2 := fun (al : alt) => forall b c ats,
      are_atoms ats ->
      map_alt (subst_var (zip_var_list (length ats) ats)) (b + c) al =
      map_alt (subst_var (zip_var_list (length ats + b) ats)) c al)...
(* Case App *)
f_equal...
apply map_ext...
(* Constr *)
f_equal...
apply map_ext...
(* Letrec *)  
f_equal...
apply map_ext_in...
rewrite <- plus_assoc...
rewrite <- plus_assoc...
(* Case Case *)
f_equal...
apply map_ext_in...
(* Lf *)
f_equal.
rewrite <- plus_assoc...
(* Alt *)
f_equal...
rewrite <- plus_assoc...
Qed.

Lemma split_atom_map_offset :
forall e b ats,
  are_atoms ats ->
  map_expr (subst_var (zip_var_list (length ats) ats)) b e =
  e~[zip_var_list (length ats + b) ats].
Proof.
isa.
assert (b = b + 0).
  trivial.
rewrite H0 at 1.  
apply split_atom_map_offset0.
trivial.
Qed.

Lemma open_inv_to_closed0 :
forall b ps e pi,
  are_atoms ps ->
  length ps <= b ->
  closed_lf 0 (Lf pi b e) ->
  closed_expr (b - length ps) (e~[zip_var_list b ps]).
Proof with isa.
isa.
inversion_clear H1...
assert (K : exists k, b = length ps + k).
  exists (b - length ps).
  intuition.
destruct K.
rewrite H1 at 2.
rewrite <- split_atom_map_offset...
assert (K : x = b - length ps).
  omega.
rewrite <- K.
rewrite H1 in H2.
apply open_inv_to_closed2...
Qed.

Lemma open_inv_to_closed :
forall ps b pi e,
  are_atoms ps ->
  length ps = b -> closed_lf 0 (Lf pi b e) ->
  closed_expr 0 (e~[zip_var_list b ps]).
Proof.
intros.
assert (R : 0 = b - length ps).
  omega.
rewrite R.
apply open_inv_to_closed0 with (pi := pi); auto.
intuition.
Qed.

Lemma open_inv_to_closed1 :
forall b e ats,
  are_atoms ats ->
  b = length ats ->
  closed_by_expr nil b e -> closed_expr 0 (e~[zip_var_list b ats]).
Proof with auto.
isa.
apply open_inv_to_closed with (pi := Update)...
constructor...
Qed.

Lemma subst_var_nil_id :
subst_var nil = id.
Proof with isa.
apply functional_extensionality...
unfold subst_var...
destruct x...
Qed.

Lemma apply_with_offset_id :
forall n, apply_with_offset id n = id.
Proof with isa.
isa.
apply functional_extensionality.
unfold apply_with_offset...
destruct x...
destruct le_lt_dec...
(* why not simpl? *)
unfold id.
f_equal.
omega.
Qed.

Ltac apply_with_offset_id_map_id := 
  rewrite apply_with_offset_id;
  apply map_id.

Lemma empty_subst :
forall e : expr, e~[nil] = e.
Proof with isa; f_equal; isa.
intro.
assert (H : forall n, map_expr (subst_var nil) n e = e).
induction e using expr_ind2 with
  (P1 := fun (lf : lambda_form) => forall n,
    map_lf (subst_var nil) n lf = lf)
  (P2 := fun (al : alt) => forall n,
    map_alt (subst_var nil) n al = al)...
destruct v...
destruct le_lt_dec...
omega.
rewrite subst_var_nil_id; apply_with_offset_id_map_id.
rewrite subst_var_nil_id; apply_with_offset_id_map_id.
generalize n; clear n.
induction ds...
rewrite arith_a_plus_Sb_EQ_Sa_plus_b.
apply IHds...
generalize n; clear n.
induction als...
apply H.
Qed.

Hint Resolve atoms_closed_app atoms_app closed_rem_args open_inv_to_closed.

Lemma closed_transfer_var :
forall mu n v qk,
  length qk <= n ->
  closed_by_var (assoc_keys mu) n v ->
  closed_by_var
    (assoc_keys (zip_var_list (length qk) qk ++ shift (length qk) mu))
    (n - length qk) v.
Proof with isa.
intros.
inversion H0.
(* case *)
cutrewrite (m + n = m + n - (n - length qk) + (n - length qk));
  try omega.
apply closed_by_var_env.
rewrite assoc_keys_app_distr.
eapply in_app_right.
cutrewrite (m + n - (n - length qk) = m + length qk);
  try omega.
apply assoc_keys_ex_value in H1.
destruct H1.
apply shift_in with (k := length qk) in H1.
eapply assoc_value_ex_key; eauto.
(* case *)
subst.
destruct (le_lt_dec (n - length qk) m).
cutrewrite (m = m - (n - length qk) + (n - length qk));
  try omega.
apply closed_by_var_env...
rewrite assoc_keys_app_distr.
apply in_app_left.
apply zip_var_list_domain; omega.
apply closed_by_var_index...
(* case *)
constructor...
Qed.

Lemma closed_transfer_vars :
forall mu n vs qk,
  length qk <= n ->
  closed_by_vars (assoc_keys mu) n vs ->
  closed_by_vars
    (assoc_keys (zip_var_list (length qk) qk ++ shift (length qk) mu))
    (n - length qk) vs.
Proof with isa.
intros.
inversion H0.
constructor...
apply closed_transfer_var...
Qed.

Lemma closed_transfer :
forall mu n f qk,
  length qk <= n ->
  closed_by_expr (assoc_keys mu) n f ->
  closed_by_expr
    (assoc_keys (zip_var_list (length qk) qk ++ shift (length qk) mu))
    (n - length qk) f.
Proof with isa.
intros.
revert n qk H H0.
induction f using expr_ind2 with
    (P1 := fun (lf : lambda_form) => forall (n : nat) (qk : list var),
      length qk <= n ->
      closed_by_lf (assoc_keys mu) n lf ->
      closed_by_lf
      (assoc_keys (zip_var_list (length qk) qk ++ shift (length qk) mu))
      (n - length qk) lf)
    (P2 := fun (al : alt) => forall (n : nat) (qk : list var),
      length qk <= n ->
      closed_by_alt (assoc_keys mu) n al ->
      closed_by_alt
      (assoc_keys (zip_var_list (length qk) qk ++ shift (length qk) mu))
      (n - length qk) al)...
(* Case App *)
inversion H0; subst.
constructor.
apply closed_transfer_var...
apply closed_transfer_vars...
(* Case Constr *)
inversion H0; subst.
constructor.
apply closed_transfer_vars...
(* Case Let *)
inversion H1; subst.
constructor;
cutrewrite (n - length qk + length ds = n + length ds - length qk);
  try omega...
apply H; try omega...
apply IHf; try omega...
(* Case Case *)
inversion H1; subst.
constructor...
(* Case Lf *)
inversion H0.
constructor...
cutrewrite (n - length qk + b = n + b - length qk);
  try omega...
apply IHf; try omega...
(* Case Alt *)
inversion H0.
constructor...
cutrewrite (n - length qk + b = n + b - length qk);
  try omega...
apply IHf; try omega...
Qed.

(** * [subst_inversion] tactic*)

(** The [subst_inversion] tactic inverts equalities of the form
[e1 = e2 ~ [beta]] to guarantee that [e2] has the same basic form (has the
same outer-most constructor) as [e1]. It also produces assumptions that
the constructor arguments are also substitutions, for example:

[[
H : Case e als = a ~ [beta] |- P a

Coq < subst_inversion H

f0 : expr,
als0 : list alt,
H : Case e als =
    Case (map_expr (subst_var beta) 0 f0)
      (map (map_alt (subst_var beta) 0) als0),
H1 : e = map_expr (subst_var beta) 0 f0,
H2 : als = map (map_alt (subst_var beta) 0) als0
|- P (Case f0 als0)
]]
*)

Lemma subst_inversion_app :
forall e beta p ps,
  App p ps = e~[beta] -> exists x, exists xs, e = App x xs.
Proof with subst; isa.
intros.
destruct e; unfold subst in H; simpl in H; try discriminate.
inversion H...
exists v.
exists v0...
Qed.

Lemma subst_inversion_constr :
forall e beta C pibeta,
  Constr C pibeta = e~[beta] -> exists ps, e = Constr C ps.
Proof with subst; isa.
intros.
destruct e; unfold subst in H; simpl in H; try discriminate.
inversion H...
exists v...
Qed.

Lemma subst_inversion_let :
forall e f lfs beta,
  Letrec lfs f = e~[beta] -> exists lfs0, exists f0, e = Letrec lfs0 f0.
Proof with subst; isa.
intros.
destruct e; unfold subst in H; simpl in H; try discriminate.
inversion H...
exists l.
exists e...
Qed.

Lemma subst_inversion_case :
forall e f als beta,
  Case f als = e~[beta] -> exists f0, exists als0, e = Case f0 als0.
Proof.
intros.
destruct e; unfold subst in H; simpl in H; try discriminate.
exists e.
exists l.
trivial.
Qed.

Ltac subst_inversion_constr_tac H :=
  let R := fresh H in
  set (R := H);
  apply subst_inversion_constr in R;
  case R;
  let vs := fresh "vs" in intro vs;
  clear R;
  let h := fresh H in intro h;
  subst.

Ltac subst_inversion_app_tac H :=
  let R := fresh H in
  set (R := H);
  apply subst_inversion_app in R;
  case R;
  let x := fresh "x" in intro x;
  let exs := fresh "exs" in intro exs;
  case exs;
  let xs := fresh "xs" in intro xs;
  clear exs;
  clear R;
  let h := fresh "alala" in intro h;
  subst;
  unfold subst in H;
  simpl in H;
  simpl in H;
  rewrite apply_with_offset_0_v in H;
  rewrite apply_with_offset_0_id in H;
  inversion H.

Ltac subst_inversion_let_tac EQe :=
  let R := fresh EQe in
  set (R := EQe);
  apply subst_inversion_let in R;
  case R;
  let lfs := fresh "lfs" in intro lfs;
  let ex := fresh "ex" in intro ex;
  case ex; clear ex;
  let e := fresh "e" in intro e;
  clear R;
  let h := fresh "eq" in intro h;
  subst;
  unfold subst in EQe;
  simpl in EQe;
  inversion EQe.

Ltac subst_inversion_case_tac EQe :=
  let R := fresh EQe in
  set (R := EQe);
  apply subst_inversion_case in R;
  case R;
  let e := fresh "f" in intro e;
  let ex := fresh "ex" in intro ex;
  case ex; clear ex;
  let als := fresh "als" in intro als;
  clear R;
  let h := fresh "eq" in intro h;
  subst;
  unfold subst in EQe;
  simpl in EQe;
  inversion EQe.

Ltac subst_inversion H :=
  first
  [ subst_inversion_constr_tac H
  | subst_inversion_app_tac H 
  | subst_inversion_let_tac H
  | subst_inversion_case_tac H ].

(** * More on [trim] *)

Lemma In_trim_assoc_keys :
forall m beta xs,
  In m (assoc_keys beta) ->
  In (Index m) xs ->
  In m (assoc_keys (trim beta xs)).
Proof with isa.
intros.
apply assoc_keys_ex_value in H.
destruct H.
apply assoc_value_ex_key with (a := x).
unfold trim.
apply <- filter_In.
split...
destruct In_dec...
Qed.

Lemma In_assoc_keys_trim :
forall m beta xs,
  In m (assoc_keys (trim beta xs)) ->
  In m (assoc_keys beta).
Proof with isa.
intros.
unfold trim in *.
apply assoc_keys_ex_value in H.
destruct H.
apply filter_In in H. 
destruct H.
apply assoc_value_ex_key with (a := x)...
Qed.

Lemma closed_trim_var :
forall beta x,
  closed_by_var (assoc_keys beta) 0 x ->
  closed_by_var (assoc_keys (trim beta (x :: nil))) 0 x.
Proof with isa.
intros.
inversion H; subst.
(* env *)
apply closed_by_var_env.
simpl_arith.
apply In_trim_assoc_keys...
(* index *)
apply closed_by_var_index...
(* atom *)
apply closed_by_var_atom...
Qed.

Lemma closed_trim_vars :
forall beta xs,
  closed_by_vars (assoc_keys beta) 0 xs ->
  closed_by_vars (assoc_keys (trim beta xs)) 0 xs.
Proof with isa.
intros.
constructor.
inversion H; subst.
intros.
dupl H1.
apply H0 in H1.
apply closed_trim_var in H1.
inversion H1; subst.
(* env *)
apply closed_by_var_env.
simpl_arith.
apply In_trim_assoc_keys...
apply In_assoc_keys_trim with (xs := Index m :: nil)...
(* index *)
apply closed_by_var_index...
(* atom *)
apply closed_by_var_atom...
Qed.

Lemma closed_trim_var_app_nil :
forall beta x,
  closed_by_expr (assoc_keys beta) 0 (App x nil) ->
  closed_by_expr (assoc_keys (trim beta (x :: nil))) 0 (App x nil).
Proof with isa.
intros.
inversion H; subst.
constructor.
apply closed_trim_var...
constructor...
contradiction.
Qed.

Lemma filter_simpl :
forall (A : Type) (a : A) (l : list A) (f : A -> bool),
  filter f (a :: l) = if f a then a :: filter f l else filter f l.
Proof.
trivial.
Qed.

Lemma find_assoc_trim_In :
forall n beta xs,
  In (Index n) xs ->
  find_assoc beta n = find_assoc (trim beta xs) n.
Proof with isa.
induction beta.
isa.
destruct a...
destruct (eq_nat_dec n n0).
(* eq *)
subst.
destruct In_dec...
  (* in *)
destruct eq_nat_dec...
case n...
  (* not in *)
tauto.
(* neq *)
destruct In_dec...
destruct eq_nat_dec...
subst...
case n1...
Qed.

Lemma find_assoc_trim :
forall n beta,
  find_assoc beta n = find_assoc (trim beta (Index n :: nil)) n.
Proof with isa.
intros.
apply find_assoc_trim_In.
auto with *.
Qed.

Lemma subst_trim_var : 
forall beta x,
  subst_var beta x = subst_var (trim beta (x :: nil)) x.
Proof with isa.
intros.
unfold subst_var.
destruct x...
rewrite <- find_assoc_trim...
Qed.

Lemma subst_trim_vars : 
forall beta xs,
  map (subst_var beta) xs = map (subst_var (trim beta xs)) xs.
Proof with isa.
intros.
apply map_ext_in...
destruct a...
rewrite <- find_assoc_trim_In...
Qed.

Lemma trim_nil:
forall vs,
  trim nil vs = nil.
Proof with isa.
intros.
unfold trim...
Qed.

Lemma trim_nil_2:
forall beta,
  trim beta nil = nil.
Proof with isa.
intros.
unfold trim.
induction beta...
destruct a...
Qed.

Lemma closed_trim_not_bound_var :
forall (beta : env) (b : nat) (v : var) (ws : vars),
  In (minus_offset b v) ws ->
  closed_by_var (assoc_keys beta) b v ->
  closed_by_var (assoc_keys (trim beta ws)) b v.
Proof with isa.
intros.
destruct v.
(* index *)
inversion H0; subst; try constructor...
apply In_trim_assoc_keys...
cutrewrite (m = m + b - b)...
omega.
(* atom *)
constructor.
Qed.

Lemma not_bound_In :
forall b vs m, 
  In (Index (m + b)) vs ->
  In m (not_bound_vars b vs).
Proof with isa.
intros.
induction vs...
destruct H.
(* left *)
subst.
clear IHvs.
unfold not_bound_var.
destruct le_lt_dec.
left; omega.
cut (~ m + b < b).
tauto.
omega.
(* right *)
destruct not_bound_var...
Qed.

Lemma trim_closed_app_var :
forall beta vs ws n v,
  closed_by_var (assoc_keys (trim beta vs)) n v ->
  closed_by_var (assoc_keys (trim beta (vs ++ ws))) n v.
Proof with isa.
intros.
inversion H; subst; [ | constructor; auto | constructor ].
apply closed_by_var_env.
clear H.
induction beta.
rewrite trim_nil in *...
destruct a...
destruct In_dec.
destruct In_dec...
destruct H0...
destruct H0...
subst.
apply in_app_left with (m := ws) in i.
tauto.
destruct In_dec...
Qed.

Lemma trim_closed_app_vars :
forall beta zs ws n vs,
  closed_by_vars (assoc_keys (trim beta vs)) n zs ->
  closed_by_vars (assoc_keys (trim beta (vs ++ ws))) n zs.
Proof with isa.
intros.
inversion H; subst.
constructor...
apply trim_closed_app_var...
Qed.

Lemma trim_closed_app :
forall e beta vs ws n,
  closed_by_expr (assoc_keys (trim beta vs)) n e ->
  closed_by_expr (assoc_keys (trim beta (vs ++ ws))) n e.
Proof with isa.
induction e using expr_ind2 with
    (P1 := fun lf : lambda_form => forall beta vs ws n,
      closed_by_lf (assoc_keys (trim beta vs)) n lf ->
      closed_by_lf (assoc_keys (trim beta (vs ++ ws))) n lf)
    (P2 := fun al : alt => forall beta vs ws n,
      closed_by_alt (assoc_keys (trim beta vs)) n al ->
      closed_by_alt (assoc_keys (trim beta (vs ++ ws))) n al);
  intros.
(* Case App *)
inversion H; subst.
constructor.
apply trim_closed_app_var...
apply trim_closed_app_vars...
(* Case Constr *)
inversion H; subst.
constructor.
apply trim_closed_app_vars...
(* Case Letrec *)
inversion H0; subst.
constructor...
(* Case Case *)
inversion H0; subst.
constructor...
(* Case Lf *)
inversion H; subst.
constructor...
(* Case Alt *)
inversion H; subst.
constructor...
Qed.

Lemma In_app_comm :
forall (A : Type) (vs ws : list A) (x : A),
  In x (vs ++ ws) ->
  In x (ws ++ vs).
Proof with isa.
intros.
apply in_app_or in H.
apply in_or_app.
tauto.
Qed.

Lemma trim_app_comm :
forall vs ws beta,
  trim beta (vs ++ ws) = trim beta (ws ++ vs).
Proof with isa.
intros.
induction beta...
destruct a.
destruct In_dec; destruct In_dec...
f_equal...
apply In_app_comm in i; apply n0 in i; contradiction.
apply In_app_comm in i; apply n0 in i; contradiction.
Qed.

Lemma trim_closed_app_2 :
forall e beta vs ws n,
  closed_by_expr (assoc_keys (trim beta ws)) n e ->
  closed_by_expr (assoc_keys (trim beta (vs ++ ws))) n e.
Proof with isa.
intros.
rewrite trim_app_comm.
apply trim_closed_app...
Qed. 

Lemma trim_in_flat_closed :
forall ws wss beta b e,
  In ws wss ->
  closed_by_expr (assoc_keys (trim beta ws)) b e ->
  closed_by_expr (assoc_keys (trim beta (flat wss))) b e.
Proof with isa.
induction wss...
contradiction.
destruct H; subst.
apply trim_closed_app...
apply trim_closed_app_2...
Qed.

Lemma closed_trim_not_bound :
forall e beta b,
  closed_by_expr (assoc_keys beta) b e ->
  closed_by_expr (assoc_keys
    (trim beta (map Index (not_bound_expr b e)))) b e.
Proof with isa.
induction e using expr_ind2 with
  (P1 := fun lf : lambda_form => forall beta b, 
    closed_by_lf (assoc_keys beta) b lf ->
    closed_by_lf (assoc_keys
      (trim beta (map Index (not_bound_lf b lf)))) b lf)
  (P2 := fun al : alt =>  forall beta b, 
    closed_by_alt (assoc_keys beta) b al ->
    closed_by_alt (assoc_keys
      (trim beta (map Index (not_bound_alt b al)))) b al);
   intros.
(* Case App *)
inversion H; subst.
constructor.
  (* var *)
inversion H2; [ | constructor | constructor ]...
apply closed_trim_not_bound_var...
rewrite map_app.
apply in_app_left.
unfold not_bound_vars...
destruct le_lt_dec...
omega.
constructor...
  (* vars *)
constructor.
intros.
inversion H3.
dupl H0.
apply H1 in H4.
inversion H4; [ | constructor | constructor ]...
subst.
apply closed_trim_not_bound_var...
rewrite map_app.
apply in_app_right.
apply in_map.
cutrewrite (m + b - b = m); try omega...
apply not_bound_In...
(* Case Constr *)
inversion H; subst.
constructor.
constructor.
intros.
inversion H1.
dupl H0.
apply H1 in H3.
inversion H3; [ | constructor | constructor ]...
subst.
apply closed_trim_not_bound_var...
apply in_map.
cutrewrite (m + b - b = m); try omega...
apply not_bound_In...
(* Case Letrec *)
inversion H0; subst.
constructor...
  (* defs *)
rewrite map_app.
destruct lf.
constructor.
apply trim_closed_app...
dupl H1.
apply H3 in H1.
apply H in H1...
inversion H1; subst.
rewrite map_flat_map.
apply trim_in_flat_closed with
  (ws := map Index (not_bound_lf (b + length ds) (Lf u b0 e0)))...
assert (not_bound_lf (b + length ds) (Lf u b0 e0) =
        not_bound_expr (b + length ds + b0) e0).
  auto.
rewrite <- H5.
apply in_map.
apply in_map...
  (* expr *)
rewrite map_app.
apply trim_closed_app_2...
(* Case Case *)
inversion H0; subst.
constructor...
  (* expr *)
rewrite map_app.
apply trim_closed_app_2...
  (* alts *)
rewrite map_app.
destruct al.
constructor.
apply trim_closed_app...
dupl H1.
apply H4 in H1.
apply H in H1...
inversion H1; subst.
rewrite map_flat_map.
apply trim_in_flat_closed with
  (ws := map Index (not_bound_alt b (Alt c b0 e0)))...
assert (not_bound_alt b (Alt c b0 e0) =
        not_bound_expr (b + b0) e0).
  auto.
rewrite <- H5.
apply in_map.
apply in_map...
(* Case Lf *)
inversion H; subst.
constructor...
(* Case Alt *)
inversion H; subst.
constructor...
Qed.

Lemma closed_trim_fv :
forall beta pi b e,
  closed_by_expr (assoc_keys beta) b e ->
  closed_by_expr (assoc_keys (trim beta (fv (Lf pi b e)))) b e.
Proof.
unfold fv.
unfold not_bound_lf.
intros.
fold (not_bound_expr (0 + b) e).
simpl.
apply closed_trim_not_bound.
auto.
Qed.

Lemma trim_fv_var :
forall beta n v vs ws,
  In (minus_offset n v) vs ->
  apply_with_offset (subst_var beta) n v =
  apply_with_offset (subst_var (trim beta (vs ++ ws))) n v.
Proof with isa.
intros.
destruct v...
destruct le_lt_dec...
apply in_app_left with (m := ws) in H.
apply find_assoc_trim_In with (beta := beta) in H.
rewrite H...
Qed.

Lemma in_not_bound_list :
forall n n0 vs,
  n <= n0 ->
  In (Index n0) vs ->
  In (Index (n0 - n)) (map Index (not_bound_vars n vs)).
Proof with isa.
intros.
induction vs...
destruct H0.
(* left *)
subst...
destruct le_lt_dec...
apply le_lt_trans with (n := n) in l...
apply n_lt_n_false in l; contradiction.
(* right *)
destruct not_bound_var...
Qed.

Lemma find_assoc_trim_app_comm :
forall vs ws beta,
  find_assoc (trim beta (vs ++ ws)) =
  find_assoc (trim beta (ws ++ vs)).
Proof with isa.
induction beta...
destruct a.
destruct In_dec; destruct In_dec...
rewrite IHbeta...
apply in_app_comm in i.
tauto.
apply in_app_comm in i.
tauto.
Qed.

Lemma subst_var_trim_app_comm :
forall beta vs ws,
  subst_var (trim beta (vs ++ ws)) =
  subst_var (trim beta (ws ++ vs)).
Proof with isa.
intros.
apply functional_extensionality...
destruct x...
rewrite find_assoc_trim_app_comm...
Qed.

Lemma trim_fv_expr_pre :
forall e n beta ws,
  map_expr (subst_var beta) n e =
  map_expr (subst_var (trim beta (map Index (not_bound_expr n e) ++ ws)))
    n e.
Proof with isa.
induction e using expr_ind2 with
    (P1 := fun (lf : lambda_form) => forall n ws beta,
      map_lf (subst_var beta) n lf =
      map_lf (subst_var
        (trim beta (map Index (not_bound_lf n lf) ++ ws))) n lf)
    (P2 := fun (al : alt) =>  forall n ws beta,
      map_alt (subst_var beta) n al =
      map_alt (subst_var
        (trim beta (map Index (not_bound_alt n al) ++ ws))) n al);
  intros; intuition; isa; f_equal...
(* [7] Case App *)
  (* [7] var *)
destruct v.
    (* Index *)
case (le_lt_dec n n0); intros.
      (* n <= n0 *)
apply trim_fv_var...
rewrite map_app.
apply in_app_left.
unfold not_bound_vars...
destruct (le_lt_dec n n0)...
omega.
      (* n0 < n *)
isa.
destruct le_lt_dec...
apply le_lt_trans with (n := n) in l...
apply n_lt_n_false in l; contradiction.
    (* Atom *)
simpl...
  (* [6] vars *)
apply map_ext_in...
destruct a.
    (* Index *)
case (le_lt_dec n n0); intros.
      (* n <= n0 *)
apply trim_fv_var...
rewrite map_app.
apply in_app_right.
apply in_not_bound_list...
      (* n0 < n *)
isa.
destruct le_lt_dec...
apply le_lt_trans with (n := n) in l...
apply n_lt_n_false in l; contradiction.
    (* Atom *)
simpl...
(* [5] Case Constr *)
apply map_ext_in...
destruct a.
  (* Index *)
case (le_lt_dec n n0); intros.
    (* n <= n0 *)
apply trim_fv_var...
apply in_not_bound_list...
    (* n0 < n *)
isa.
destruct le_lt_dec...
apply le_lt_trans with (n := n) in l...
apply n_lt_n_false in l; contradiction.
    (* Atom *)
simpl...
(* [4] Case Letrec *)
  (* [4] defs *)
apply map_ext_in...
rewrite map_app.
rewrite app_ass.
remember (map Index (not_bound_expr (n + length ds) e) ++ ws) as wws.
remember (n + length ds) as m.
clear Heqm Heqwws IHe e.
rewrite flat_map_flat_map.
dupl H0.
apply flat_map_is_app with (f := not_bound_lf m) in H1.
destruct H1.
destruct H1.
rewrite H1.
rewrite map_app.
rewrite map_app.
cutrewrite (
  (map Index x ++ map Index (not_bound_lf m a) ++ map Index x0) ++ wws =
   map Index x ++ map Index (not_bound_lf m a) ++ map Index x0 ++ wws).
rewrite subst_var_trim_app_comm.
rewrite app_ass...
    (* cutrewrite *)
rewrite app_ass.
rewrite app_ass...
  (* [3] expr *)
rewrite map_app.
rewrite subst_var_trim_app_comm.
rewrite <- app_ass.
rewrite subst_var_trim_app_comm...
(* [2] Case Letrec *)
  (* [2] expr *)
rewrite map_app.
rewrite subst_var_trim_app_comm.
rewrite <- app_ass.
rewrite subst_var_trim_app_comm...
  (* [1] alts *)
apply map_ext_in...
rewrite map_app.
rewrite app_ass.
rewrite flat_map_flat_map.
dupl H0.
apply flat_map_is_app with (f := not_bound_alt n) in H1.
destruct H1.
destruct H1.
rewrite H1.
rewrite map_app.
rewrite map_app.
rewrite app_ass.
rewrite subst_var_trim_app_comm.
rewrite app_ass.
rewrite app_ass...
Qed.

Lemma trim_fv_expr :
forall e n beta,
  map_expr (subst_var beta) n e =
  map_expr (subst_var (trim beta (map Index (not_bound_expr n e)))) n e.
Proof with isa.
intros.
cutrewrite (map Index (not_bound_expr n e) =
            map Index (not_bound_expr n e) ++ nil);
  auto with *.
apply trim_fv_expr_pre.
Qed.

Lemma trim_fv_lf :
forall lf beta,
  map_lf (subst_var beta) 0 lf =
  map_lf (subst_var (trim beta (fv lf))) 0 lf.
Proof with isa.
isa.
destruct lf...
f_equal.
unfold fv...
apply trim_fv_expr.
Qed.
