(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains the definition of the explicit-environment
semantics and proof of its equivalence with the argument-accumulating
semantics. *)

Require Export Heaps.
Require Export Sem02.
Require Import Min.

(** * Explicit Environment Semantics *)

Reserved Notation "($ a $ b $ g $ e ↓↓↓ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive EES : heapB -> expr -> env -> vars -> heapB -> expr -> env ->
  vars -> Prop :=

| E_Con : forall Gamma C pi sigma,
  ($ Gamma $ Constr C pi $ sigma $ nil ↓↓↓ Gamma $ Constr C pi $ sigma $ nil)

| E_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ Gamma $ App x nil $ sigma $ sigma_xm ++ qn ↓↓↓ Delta $ w $ rho $ rs) ->
  ($ Gamma $ App x xm  $ sigma $ qn             ↓↓↓ Delta $ w $ rho $ rs)

| E_App1 : forall Gamma p x pn m e sigma tau,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ Gamma $ App x nil $ sigma $ pn ↓↓↓ Gamma $ App x nil $ sigma $ pn)

| E_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn ↓↓↓ Delta $ w $ rho $ rs) ->
  ($ Gamma $ App x nil $ sigma                                       $ pn         ↓↓↓ Delta $ w $ rho $ rs)

| E_App4 : forall Gamma Delta sigma tau rho e p x C xs,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ Gamma $ e         $ tau   $ nil ↓↓↓ Delta                                            $ Constr C xs $ rho $ nil) ->
  ($ Gamma $ App x nil $ sigma $ nil ↓↓↓ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil)

| E_App5 : forall Gamma Delta Theta x p pn y q qk e f n w rs sigma rho nu
  mu tau,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Gamma p = Some (Lf_u e, tau) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ Gamma $ e         $ tau   $ nil      ↓↓↓ Delta $ App y nil      $ rho $ qk) ->
  ($ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho   $ qk ++ pn ↓↓↓ Theta $ w              $ nu  $ rs) ->
  ($ Gamma $ App x nil $ sigma $ pn       ↓↓↓ Theta $ w              $ nu  $ rs)

| E_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs
    ↓↓↓ Delta $ w $ rho $ ss) ->
  ($ Gamma $ Letrec lfs e $ sigma $ rs ↓↓↓ Delta $ w $ rho $ ss)

| E_Case_of : forall Gamma Delta Theta b e e0 als ys w c c0 rho_ys rs qs
  sigma rho nu,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Gamma $ e          $ sigma                                  $ nil ↓↓↓ Delta $ Constr c ys $ rho $ nil) ->
  ($ Delta $ e0         $ zip_var_list b rho_ys ++ shift b sigma $ qs  ↓↓↓ Theta $ w           $ nu $ rs) ->
  ($ Gamma $ Case e als $ sigma                                  $ qs  ↓↓↓ Theta $ w           $ nu $ rs)

where "($ a $ b $ g $ e ↓↓↓ c $ d $ h $ f )" := (EES a b g e c d h f).

Hint Constructors EES.

(** * [heapB_ok] *)

Definition heapB_ok (hb : heapB) : Prop :=
(forall n lf tau, hb n = Some (lf, tau) -> no_atoms_lf lf) /\
(forall n lf tau, hb n = Some (lf, tau) ->
  closed_by_lf (assoc_keys tau) 0 lf).

Lemma empty_ok:
heapB_ok emptyB.
Proof.
unfold heapB_ok.
split; isa;
unfold emptyB in *; discriminate.
Qed.

(** * Properties of the semantics *)

Lemma no_atoms_EES_no_atoms_aux:
forall Xi a beta Ps Omega c xi Qs,
  ($ Xi $ a $ beta $ Ps ↓↓↓ Omega $ c $ xi $ Qs) ->
  no_atoms a ->
  (forall n lf tau, Xi n = Some (lf, tau) -> no_atoms_lf lf) ->
  no_atoms c /\
  (forall n lf tau, Omega n = Some (lf, tau) -> no_atoms_lf lf).
Proof with isa; eauto.
isa.
induction H...
(* [6] Case *)
apply IHEES...
constructor...
inversion H0.
trivial.
constructor...
contradiction.
(* [5] Case *)
apply IHEES...
assert (no_atoms_lf (Lf_n m e))...
inversion_clear H5...
(* [4] Case *)
split...
apply IHEES...
assert (no_atoms_lf (Lf_u e))...
inversion_clear H4...
unfold setB in H4.
destruct eq_nat_dec.
subst.
inversion_clear H4.
constructor.
apply IHEES...
assert (no_atoms_lf (Lf_u e))...
inversion_clear H4...
assert (no_atoms_lf (Lf_u e))...
inversion_clear H5...
apply IHEES in H6...
destruct H6...
(* [3] Case *)
apply IHEES2...
assert (no_atoms_lf (Lf_u e))...
inversion_clear H8...
apply IHEES1...
unfold setB in H8.
assert (no_atoms_lf (Lf_u e))...
inversion_clear H9.
destruct eq_nat_dec.
subst.
inversion_clear H8.
assert (no_atoms_lf (Lf_n n f)).
  apply IHEES1 in H10...
  destruct H10...
inversion_clear H8.
constructor...
apply IHEES1 in H10;
  [destruct H10; eapply H10 | eapply H1 ]...
(* [2] Case *)
inversion H0; subst.
apply IHEES...
destruct (In_dec eq_nat_dec n ats).
apply allocB_in in H4...
eapply in_map_iff in H4.
destruct H4.
destruct H4.
inversion H4; subst...
rewrite map_length...
rewrite allocB_nin in H4...
(* [1] Case *)
inversion H0; subst.
apply IHEES2...
apply In_select_case in H3.
apply H9 in H3.
inversion H3; subst...
apply IHEES1 in H8...
destruct H8...
Qed.

Lemma no_atoms_EES_no_atoms :
forall Xi a beta Ps Omega c xi Qs,
  ($ Xi $ a $ beta $ Ps ↓↓↓ Omega $ c $ xi $ Qs) ->
  no_atoms a ->
  (forall n lf tau, Xi n = Some (lf, tau) -> no_atoms_lf lf) ->
  no_atoms c.
Proof with eauto.
intros.
eapply no_atoms_EES_no_atoms_aux in H1...
destruct H1...
Qed.

(** * [only_atoms] restriction *)

Definition oa_heap (hb : heapB) := 
forall v lf tau, hb v = Some (lf, tau) ->
  forall n a, In (n, a) tau -> is_atom a.

Definition oa_env (e : env) :=
forall n a, In (n, a) e -> is_atom a.

Definition oa_accum (vs : vars) :=
are_atoms vs.

Inductive only_atoms (hb : heapB) (e : env) (vs : vars) : Prop :=
| oa_c : oa_heap hb -> oa_env e -> oa_accum vs -> only_atoms hb e vs.

Ltac oa_inversion OA :=
case OA;
  let  a := fresh "OA_ACCUM"
  with b := fresh "OA_ENV"
  with c := fresh "OA_HEAP"
  in intros c b a.

Lemma oa_env_map :
forall sigma xm sigma_xm,
  oa_env sigma ->
  env_map sigma xm = Some sigma_xm ->
  oa_accum sigma_xm.
Proof with isa; try discriminate.
isa.
revert sigma_xm H0.
induction xm...
(* nil *)
inversion H0...
unfold oa_accum...
apply atoms_nil.
(* cons *)
destruct a...
assert (exists s, env_map sigma xm = Some s).
  remember_destruct (env_map sigma xm).
  exists v...
  rewrite <- X in H0...
destruct H1.
rewrite H1 in *.
assert (exists p, find_assoc sigma n = Some p).
  remember_destruct (find_assoc sigma n).
  exists v...
  rewrite <- X in H0...
destruct H2.
rewrite H2 in *.
inversion H0.
assert (oa_accum x).
  apply IHxm...
apply find_assoc_in in H2.
unfold oa_env in H.
unfold oa_accum.
unfold are_atoms...
destruct H5.
subst.
eapply H; eauto.
unfold oa_accum in H3.
unfold are_atoms in H3.
apply H3...
Qed.

Create HintDb oa.

Lemma oa_accum_app :
forall vs ws,
  oa_accum vs ->
  oa_accum ws ->
  oa_accum (vs ++ ws).
Proof.
intros.
unfold oa_accum in *.
apply atoms_app; auto.
Qed.

Lemma oa_env_app :
forall sigma tau,
  oa_env sigma ->
  oa_env tau ->
  oa_env (sigma ++ tau).
Proof with intros; eauto.
intros.
unfold oa_env in *...
apply in_app_or in H1.
destruct H1...
Qed.

Lemma oa_env_shift :
forall m tau,
  oa_env tau -> oa_env (shift m tau).
Proof with intros; eauto.
intros.
unfold oa_env in *...
apply In_shift in H0...
Qed.

Lemma oa_heap_val :
forall Gamma p lf tau,
  Gamma p = Some (lf, tau) ->
  oa_heap Gamma ->
  oa_env tau.
Proof with eauto.
intros.
unfold oa_heap in H0.
unfold oa_env...
Qed.

Lemma oa_accum_nil :
oa_accum nil.
Proof.
unfold oa_accum.
unfold are_atoms.
intros.
inversion H.
Qed.

Lemma oa_accum_skipn :
forall ps n,
  oa_accum ps ->
  oa_accum (skipn n ps).
Proof with isa.
intros.
unfold oa_accum in *.
apply atoms_skipn...
Qed.

Hint Resolve
  atoms_skipn     In_zip_var_list
  oa_env_map      oa_accum_app
  oa_env_app      oa_env_shift
  oa_heap_val     oa_accum_nil
  oa_accum_skipn
: oa.

Lemma oa_empty:
oa_heap emptyB.
Proof.
unfold oa_heap.
unfold emptyB.
intros; discriminate.
Qed.

Lemma oa_empty_nil_nil:
only_atoms emptyB nil nil.
Proof.
constructor.
apply oa_empty.
unfold oa_env; intros; inversion H.
auto with oa.
Qed.

Lemma oa_accum_map_subst_var :
forall beta x xs,
  closed_by_expr (assoc_keys beta) 0 (App x xs) ->
  oa_env beta ->
  oa_accum (map (subst_var beta) xs).
Proof with auto with oa.
intros.
induction xs...
simpl.
inversion H; subst.
unfold oa_accum.
inversion H4.
unfold are_atoms.
intros.
destruct (eq_var_dec a0 (subst_var beta a)).
(* eq *)
subst.
elim H1 with (v := a); isa...
apply find_assoc_in_keys_ex_value in H5.
destruct H5.
rewrite <- plus_n_O.
rewrite H5.
apply find_assoc_in in H5.
unfold oa_env in H0.
eapply H0; eauto.
inversion H5.
(* neq *)
inversion H2...
  (* case *)
destruct n...
  (* case *)
fold (In a0 (map (subst_var beta) xs)) in H5.
assert (closed_by_expr (assoc_keys beta) 0 (App x xs)).
  constructor...
  constructor.
  intros.
  apply H1...
  right...
apply IHxs in H6...
Qed.

Lemma oa_setB :
forall Delta a lf mu,
  oa_env mu ->
  oa_heap Delta ->
  oa_heap (setB Delta a (lf, mu)).
Proof with eauto with oa.
intros.
unfold oa_heap in *.
intros.
unfold setB in H1.
destruct eq_nat_dec...
inversion H1; subst...
Qed.

Lemma oa_env_zip_var_list :
forall qk n,
  oa_accum qk ->
  oa_env (zip_var_list n qk).
Proof with eisa; auto with oa.
intros.
unfold oa_env...
unfold oa_accum in H.
unfold are_atoms in H.
apply H.
eapply In_zip_var_list...
Qed.

Hint Resolve oa_setB oa_env_zip_var_list : oa.

Lemma oa_env_trim :
forall beta xs,
  oa_env beta ->
  oa_env (trim beta xs).
Proof with eisa.
intros.
unfold trim.
unfold oa_env in *...
apply filter_In in H0.
destruct H0...
Qed.

Hint Resolve oa_env_trim : oa.

Lemma trim_app_distr :
forall beta tau vs,
  trim (beta ++ tau) vs = trim beta vs ++ trim tau vs.
Proof with isa.
induction beta...
destruct a.
destruct In_dec...
f_equal...
Qed.

Lemma In_trim :
forall beta n a vs,
  In (n, a) (trim beta vs) ->
  In (n, a) beta.
Proof with isa.
intros.
unfold trim in *.
apply filter_In in H.
destruct H...
Qed.

Lemma only_atoms_EES_only_atoms :
forall Xi a beta Ps Omega c xi Qs,
  ($ Xi $ a $ beta $ Ps ↓↓↓ Omega $ c $ xi $ Qs) ->
  forall (OA : only_atoms Xi beta Ps),
  only_atoms Omega xi Qs.
Proof with eauto with oa.
intros.
oa_inversion OA.
induction H.
(* [8] *)
constructor...
(* [7] *)
apply IHEES...
constructor...
(* [6] *)
constructor...
(* [5] *)
apply IHEES...
constructor...
apply oa_env_app...
unfold oa_env.
intros.
apply In_zip_var_list in H3.
apply In_firstn in H3...
unfold oa_accum...
apply oa_env_app...
unfold oa_env.
intros.
apply In_zip_var_list in H3.
apply In_firstn in H3...
unfold oa_accum...
(* [4] *)
elim IHEES...
constructor...
constructor...
(* [3] *)
elim IHEES1; isa...
apply IHEES2...
constructor...
apply oa_setB...
apply oa_env_trim...
apply oa_setB...
apply oa_env_trim...
constructor...
(* [2] *)
assert (oa_heap
          (allocB Gamma ats
             (map
                (fun lf : lambda_form =>
                 (lf, trim
                 (zip_var_list (length lfs) (map Atom ats) ++
                 shift (length lfs) sigma) (fv lf))) lfs))).
  unfold oa_heap.
  isa.
  destruct (In_dec eq_nat_dec v ats)...
    (* in *)
  apply allocB_in in H2...
  eapply in_map_iff in H2.
  destruct H2.
  destruct H2.
  inversion H2; subst; clear H2...
  rewrite trim_app_distr in H3.
  apply in_app_or in H3.
  destruct H3.
  apply In_trim in H2.
  apply In_zip_var_list in H2.
  apply in_map_iff in H2.
  do 2 destruct H2.
  destruct a.
  discriminate.
  simpl...
  apply In_trim in H2.
  apply oa_env_shift with (m := length lfs) in OA_ENV.
  unfold oa_env in OA_ENV...
  rewrite map_length...
    (* not in *)
  rewrite allocB_nin in H2...
assert (oa_env
          (zip_var_list (length lfs) (map Atom ats) ++
           shift (length lfs) sigma)).
  apply oa_env_app...
  apply oa_env_zip_var_list.
  unfold oa_accum.
  apply atoms_map_atom.
assert (oa_accum rs)...
apply IHEES...
constructor...
(* [1] *)
elim IHEES1; isa...
apply IHEES2...
constructor...
constructor...
Qed.

Lemma subst_var_no_index :
forall sigma n,
  oa_env sigma ->
  is_atom (subst_var sigma (Index n)) \/
  subst_var sigma (Index n) = Index n.
Proof with eisa.
intros.
destruct (In_dec eq_nat_dec n (assoc_keys sigma)).
(* in *)
left.
unfold subst_var.
apply find_assoc_in_keys_ex_value in i.
destruct i.
rewrite H0.
apply find_assoc_in in H0.
unfold oa_env in H.
eapply H...
(* not in *)
right.
apply find_assoc_notin in n0.
unfold subst_var.
rewrite n0...
Qed.

Lemma subst_lemma :
forall e m tau pn,
  oa_env tau ->
  m >= length pn ->
  (e ~ [shift m tau]) ~ [zip_var_list m pn] =
  e ~ [zip_var_list m pn ++ shift m tau].
Proof with isa.
intros.
unfold subst.
rewrite map_expr_compose.
f_equal.
apply functional_extensionality.
intro v.
unfold compose.
destruct v.
(* Index *)
destruct (le_lt_dec m n).
  (* <= *)
rewrite subst_var_app_shift_ge; auto.
apply oa_env_shift with (m := m) in H.
apply subst_var_no_index with (n := n) in H.
destruct H.
   (* left *)
to_atom (subst_var (shift m tau) (Index n)).
apply subst_var_atom.
   (* right *)
rewrite H.
cutrewrite (zip_var_list m pn = zip_var_list m pn ++ shift m nil).
apply subst_var_app_shift_ge with (tau := shift 0 nil)...
simpl.
apply app_nil_end.
  (* > *)
rewrite shift_lt_subst_var_id; try auto.
rewrite subst_var_app_shift_lt...
(* Atom *)
unfold compose.
do 3 rewrite subst_var_atom...
Qed.

Lemma apply_with_offset_shift :
forall m n v beta,
  oa_env beta ->
  apply_with_offset (subst_var beta) (m + n) v =
  apply_with_offset (subst_var (shift m beta)) n v.
Proof with eisa.
intros.
unfold apply_with_offset.
destruct v...
destruct le_lt_dec.
unfold plus_offset.
unfold subst_var.
unfold minus_offset.
cutrewrite (n0 - (m + n) = n0 - n - m); try omega.
rewrite find_assoc_shift.
remember (find_assoc (shift m beta) (n0 - n)) as F.
assert (forall v, F = Some v -> is_atom v).
  intros.
  symmetry in HeqF.
  subst.
  apply find_assoc_in in H0.
  apply oa_env_shift with (m := m) in H.
  unfold oa_env in H...
remember_destruct F.
assert (is_atom v)...
destruct v; try contradiction...
destruct le_lt_dec.
f_equal.
assert (n < n).
  omega.
apply n_lt_n_false in H2; contradiction.
destruct le_lt_dec; f_equal; omega...
omega.
destruct le_lt_dec...
assert (n0 - n < m).
  omega.
rewrite find_assoc_shift_lt; try omega...
f_equal.
omega.
Qed.

Lemma map_expr_shift :
forall beta e m n,
  oa_env beta ->
  map_expr (subst_var beta) (m + n) e =
  map_expr (subst_var (shift m beta)) n e.
Proof with isa.
intro beta.
induction e using expr_ind2 with
    (P1 := fun (lf : lambda_form) => forall m n,
      oa_env beta ->
      map_lf (subst_var beta) (m + n) lf =
      map_lf (subst_var (shift m beta)) n lf)
    (P2 := fun (al : alt) => forall m n,
      oa_env beta ->
      map_alt (subst_var beta) (m + n) al =
      map_alt (subst_var (shift m beta)) n al);
  intros; try unfold subst; simpl; try f_equal;
  try rewrite <- plus_assoc; isa;
  try apply map_ext_in; isa;
  try apply map_ext; isa;
  try apply apply_with_offset_shift...
Qed.

Lemma subst_shift :
forall beta m e,
  oa_env beta ->
  map_expr (subst_var beta) m e = e~[shift m beta].
Proof with isa.
intros.
assert (m = m + 0); try omega.
rewrite H0 at 1.
apply map_expr_shift...
Qed.

Lemma alloc_similar_no_trim :
forall (lfsF : defs) atsF beta
(LENGTHF : length lfsF = length atsF)
ats XiP Gamma lfs pi0 pi1 b0 b1 e tau etau a
(SIMILAR : similar Gamma XiP)
(LENGTH : length ats = length lfs)
(OA_ENV : oa_env beta)
(B : allocB XiP ats
       (map
          (fun lf : lambda_form =>
           (lf,
           zip_var_list (length lfsF) (map Atom atsF) ++
           shift (length lfsF) beta)) lfs) a = Some (Lf pi1 b1 e, tau))
(A : allocA Gamma (map Atom ats)
       (map (subst_lf (zip_var_list (length lfsF) (map Atom atsF)))
          (map (map_lf (subst_var beta) (length lfsF)) lfs)) (Atom a) =
     Some (Lf pi0 b0 etau)),
pi0 = pi1 /\ b0 = b1 /\ etau = e~[shift b1 tau].
Proof with eisa.
induction ats.
(* [2] nil *)
isa.
destruct lfs; simpl in *; try discriminate...
unfold allocA in A...
unfold allocB in B...
destruct SIMILAR.
destruct H0...
(* [1] cons *)
isa.
destruct lfs; simpl in *; try discriminate...
unfold allocA in A...
unfold allocB in B...
destruct (eq_nat_dec a a0); try subst a0... 
  (* eq *)
unfold setA in A.
unfold setB in B.
destruct eq_var_dec; try tauto...
destruct eq_nat_dec; try tauto...
destruct l.
inversion A; subst.
inversion B; subst.
split...
split...
rewrite subst_shift.
rewrite subst_shift...
rewrite shift_app_distr.
rewrite shift_zip_var_list; try (rewrite map_length; omega).
rewrite shift_cummulative.
rewrite plus_comm.
apply subst_lemma; try (rewrite map_length; omega)...
unfold oa_env...
apply In_zip_var_list in H.
apply in_map_iff in H.
do 2 destruct H.
subst.
unfold is_atom...
  (* neq *)
unfold allocA in IHats.
unfold allocB in IHats.
unfold setA in *.
unfold setB in *.
assert (a0 <> a); auto.
destruct eq_var_dec; try tauto...
destruct eq_nat_dec; try tauto...
inversion e0; tauto.
destruct eq_nat_dec; try tauto...
Qed.

Lemma trim_fv :
forall e b k atsF pi beta
  (OA : oa_env beta),
  k >= length atsF ->
  e~[shift b (trim
      (zip_var_list k (map Atom atsF) ++
       shift k beta) (fv (Lf pi b e)))] =
  e~[shift b (zip_var_list k (map Atom atsF) ++
       shift k beta)].
Proof with isa.
intros.
assert (map_lf (subst_var (zip_var_list k (map Atom atsF) ++
    shift k beta)) 0 (Lf pi b e) =
    map_lf (subst_var (trim (zip_var_list k (map Atom atsF) ++
    shift k beta) (fv (Lf pi b e)))) 0 (Lf pi b e)).
  apply trim_fv_lf.
assert (OA2 : oa_env (zip_var_list k (map Atom atsF) ++ shift k beta)).
  apply oa_env_app.
  unfold oa_env...
  apply In_zip_var_list in H1.
  apply in_map_iff in H1.
  destruct H1.
  destruct H1.
  subst...
  apply oa_env_shift...
simpl in H0.
inversion H0; subst.
unfold subst.
assert (H1 : b = b + 0); auto with arith.
rewrite H1 in H2 at 1 3.
rewrite map_expr_shift in H2...
rewrite map_expr_shift in H2.
symmetry in H2...
apply oa_env_trim...
Qed.

(** * Completeness *)

Lemma alloc_similar :
forall (lfsF : defs) atsF beta
(LENGTHF : length lfsF = length atsF)
ats XiP Gamma lfs pi0 pi1 b0 b1 e tau etau a
(SIMILAR : similar Gamma XiP)
(LENGTH : length ats = length lfs)
(OA_ENV : oa_env beta)
(B : allocB XiP ats
       (map
          (fun lf : lambda_form =>
           (lf, trim
             (zip_var_list (length lfsF) (map Atom atsF) ++
             shift (length lfsF) beta) (fv lf))) lfs) a =
           Some (Lf pi1 b1 e, tau))
(A : allocA Gamma (map Atom ats)
       (map (subst_lf (zip_var_list (length lfsF) (map Atom atsF)))
          (map (map_lf (subst_var beta) (length lfsF)) lfs)) (Atom a) =
     Some (Lf pi0 b0 etau)),
pi0 = pi1 /\ b0 = b1 /\ etau = e~[shift b1 tau].
Proof with eisa.
induction ats...
(* [2] nil *)
destruct lfs; simpl in *; try discriminate...
unfold allocA in A...
unfold allocB in B...
destruct SIMILAR.
destruct H0...
(* [1] cons *)
destruct lfs; simpl in *; try discriminate...
unfold allocA in A...
unfold allocB in B...
destruct (eq_nat_dec a a0); try subst a0... 
  (* eq *)
unfold setA in A.
unfold setB in B.
destruct eq_var_dec; try tauto...
destruct eq_nat_dec; try tauto...
destruct l.
inversion A; subst.
inversion B; subst.
split...
split...
rewrite trim_fv; try omega...
rewrite subst_shift.
rewrite subst_shift...
rewrite shift_app_distr.
rewrite shift_zip_var_list; try (rewrite map_length; omega).
rewrite shift_cummulative.
rewrite plus_comm.
apply subst_lemma; try (rewrite map_length; omega)...
unfold oa_env...
apply In_zip_var_list in H.
apply in_map_iff in H.
destruct H.
destruct H.
subst.
unfold is_atom...
  (* neq *)
unfold allocA in IHats.
unfold allocB in IHats.
unfold setA in *.
unfold setB in *.
assert (a0 <> a); auto.
destruct eq_var_dec; try tauto...
destruct eq_nat_dec; try tauto...
inversion e0; tauto.
destruct eq_nat_dec; try tauto...
Qed.

Lemma select_case_subst :
forall als als0 c c0 b e beta
  (OA : oa_env beta),
  select_case als c = Some (Alt c0 b e) ->
  als = map (map_alt (subst_var beta) 0) als0 ->
  exists e0,
  select_case als0 c = Some (Alt c0 b e0) /\ 
  e = e0~[shift b beta].
Proof with isa.
induction als...
discriminate.
destruct als0...
discriminate.
destruct a.
destruct a0.
destruct eq_nat_dec.
(* c = c1 *)
inversion H0; subst.
inversion H; subst; clear H.
destruct eq_nat_dec; try tauto.
clear e.
exists e1.
split...
apply subst_shift...
(* c <> c1 *)
inversion H0; subst.
destruct eq_nat_dec; subst...
tauto.
Qed.

Lemma lf_subst_lemma :
forall ats lfs sigma,
  oa_env sigma ->
  length lfs = length ats ->
  map (subst_lf (zip_var_list (length lfs) (map Atom ats) ++
    shift (length lfs) sigma)) lfs =
  map (subst_lf (zip_var_list (length lfs) (map Atom ats)))
       (map (map_lf (subst_var sigma) (length lfs)) lfs).
Proof with isa.
intros.
rewrite map_map.
apply map_ext_in...
destruct a.
unfold subst_lf...
f_equal...
rewrite subst_shift.
cutrewrite (b = b + 0)...
rewrite map_expr_shift...
rewrite map_expr_shift...
rewrite map_expr_shift...
simpl_arith.
rewrite shift_app_distr.
rewrite shift_cummulative.
rewrite shift_zip_var_list.
rewrite plus_comm at 1.
rewrite <- subst_lemma.
unfold subst.
cutrewrite (b + length lfs = length lfs + b)...
(* premises *)
omega.
trivial.
rewrite map_length; omega.
rewrite map_length; omega.
auto with oa.
apply oa_env_zip_var_list.
unfold oa_accum.
apply atoms_map_atom...
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list.
unfold oa_accum.
apply atoms_map_atom...
Qed.

Lemma select_case_subst_right :
forall als c c0 b e beta
  (OA : oa_env beta),
  select_case als c = Some (Alt c0 b e) ->
  select_case (map (map_alt (subst_var beta) 0) als) c =
    Some (Alt c0 b (e~[shift b beta])).
Proof with isa.
induction als...
discriminate.
destruct a...
destruct eq_nat_dec...
inversion_clear H.
f_equal...
f_equal...
apply subst_shift...
Qed.

Lemma oa_accum_map :
forall vs,
  oa_accum vs -> 
  exists ns, vs = map Atom ns.
Proof with isa.
intros.
induction vs.
(* nil *)
exists nil...
(* cons *)
unfold oa_accum in *.
dupl H.
apply atoms_head in H.
to_atom a.
apply atoms_tail in H0.
intuition.
destruct H1.
exists (a :: x)...
f_equal...
Qed.

Proposition EES_complete :
forall Xi Omega abeta Ps Qs cxi,
    ($ Xi $ abeta $ Ps ↓↓ Omega $ cxi $ Qs) ->
    forall a beta,
    closed_by_expr (assoc_keys beta) 0 a ->
    abeta = a~[beta] ->
    no_atoms a ->
  forall XiP, similar Xi XiP -> heapB_ok XiP ->
  forall (ONLYATOMS : only_atoms XiP beta Ps),
  exists OmegaP, exists xi, exists c,
    similar Omega OmegaP /\
    ($ XiP $ a $ beta $ Ps ↓↓↓ OmegaP $ c $ xi $ Qs) /\
    closed_by_expr (assoc_keys xi) 0 c /\
    cxi = c~[xi] /\
    heapB_ok OmegaP.
Proof with isa.
intros ? ? ebeta ? ? ? H.
dupl H. rename H0 into CASE.
induction H; intros a beta CBY EQe NOATOMS...
(* [8] Case Con *)
subst_inversion EQe.
exists XiP.
exists beta.
exists (Constr C vs)...
(* [7] Case Accum *)
subst_inversion EQe.
apply IHAAS with (XiP := XiP) (beta := beta) (a := App x nil) in H0...
  (* thesis *)
destruct H0 as [x0 [x1 [ x2 []]]].
destruct H3.
destruct H6.
destruct H7.
exists x0.
exists x1.
exists x2.
    (* similar *)
split...
    (* reduction *)
split.
eapply E_Accum with (sigma_xm := map (subst_var beta) xs).
      (* xs <> nil *)
eapply map_neq_nil; eauto.
      (* env_map *)
inversion_clear CBY.
apply env_map_map_subst...
inversion_clear NOATOMS...
      (* premise *)
rewrite H5 in H3.
apply H3.
    (* closed, subst and heap_ok*)
auto.
  (* premises of the IH *)
    (* closed_by_expr *)
inversion_clear CBY.
constructor...
constructor...
contradiction.
    (* subst *)
unfold subst; subst...
rewrite apply_with_offset_0_v...
    (* no_atoms *)
inversion_clear NOATOMS.
constructor...
constructor; isa; contradiction.
    (* only_atoms *)
oa_inversion ONLYATOMS.
constructor; auto with oa.
apply oa_accum_app...
subst; apply oa_accum_map_subst_var with (x := x)...
(* [6] Case App1 *)
subst_inversion EQe.
destruct xs; [ | discriminate ]...
exists XiP.
exists beta.
exists (App x nil).
  (* similar *)
split...
  (* reduction *)
split...
dupl H.
apply similar_dom_atom with (GammaP := XiP) in H3...
destruct p; try contradiction...
similar_value H XiP.
apply E_App1 with (p := a) (m := m) (e := x0) (tau := x1)...
    (* env_find *)
apply subst_var_env_find...
inversion NOATOMS...
  (* closed *)
split...
  (* subst *)
split.
unfold subst; subst...
rewrite apply_with_offset_0_v...
  (* heap_ok *)
auto.
(* [5] Case App2_5 *)
subst_inversion EQe.
dupl H.
apply similar_dom_atom with (GammaP := XiP) in H4...
destruct p; try contradiction...
similar_value H XiP.
rename e into etau.
rename x1 into tau.
rename x0 into e.
apply IHAAS with (XiP := XiP) (a := e)
  (beta := zip_var_list m (firstn m pn) ++ shift m tau) in H1...
  (* thesis *)
clear IHAAS.
destruct H1 as [x0 [x1 [x2 []]]].
destruct H8.
exists x0.
exists x1.
exists x2.
    (* similar *)
split...
    (* reduction *)
split.
destruct xs; [ | discriminate ]...
eapply E_App2_5 with (sigma := beta) (x := x) (p := a) in H8...
      (* env_find *)
apply subst_var_env_find...
inversion NOATOMS...
    (* closed, subst and keap_ok *)
auto.
  (* premises of the IH *)
    (* closed_by_expr *)
inversion_clear H3.
apply H9 in H.
inversion H; subst.
clear IHAAS H1.
simpl in H10.
assert (ZER : 0 = length (firstn m pn) - length (firstn m pn)).
  auto with *.
assert (LEN : m = length (firstn m pn)).
  symmetry.
  apply firstn_le_length...
rewrite LEN at 1.
rewrite LEN at 3.
rewrite LEN in H10.
rewrite ZER.
apply closed_transfer...
    (* subst *)
rewrite H7.
apply subst_lemma.
oa_inversion ONLYATOMS.
eapply oa_heap_val; eauto.
rewrite firstn_length.
auto with arith.
    (* no_atoms *)
inversion_clear H3.
set (lf := Lf Dont_update m e).
assert (no_atoms_lf lf).
  eapply H8.
  apply H.
inversion_clear H3...
    (* only_atoms *)
oa_inversion ONLYATOMS.
constructor...
apply oa_env_app...
  unfold oa_env...
  apply In_zip_var_list in H8.
  apply In_firstn in H8...
apply oa_env_shift.
eapply oa_heap_val; eauto.
apply oa_accum_skipn...
(* [4] Case App4 *)
subst_inversion EQe.
destruct xs; [ | discriminate ]...
dupl H.
apply similar_dom_atom with (GammaP := XiP) in H3...
destruct p; try contradiction...
similar_value H XiP.
rename e into etau.
rename x0 into e.
rename x1 into tau.
apply IHAAS with (XiP := XiP) (a := e) (beta := tau) in H0...
  (* thesis *)
destruct H0 as [x0 [x1 [x2 []]]].
destruct H7.
destruct H8.
destruct H9.
subst_inversion H9.
apply E_App4 with (x := x) (sigma := beta) (p := a) in H7... (* A *)
exists (setB x0 a (Lf_n 0 (Constr C vs), trim x1 vs)).
exists x1.
exists (Constr C vs).
    (* similar *)
split...
unfold similar.
      (* similar 1 *)
split.
intro.
rewrite <- H4.
unfold setA.
destruct eq_var_dec; [ discriminate | ]...
inversion_clear H0.
apply H6.
      (* similar 2 *)
split.
intro.
rewrite <- H4.
unfold setA.
unfold setB.
destruct eq_nat_dec; destruct eq_var_dec.
subst; split; intro; discriminate.
subst; destruct n; auto.
inversion e0; tauto.
inversion_clear H0.
inversion_clear H11.
apply H0.
      (* similar 3 *)
inversion_clear H0.
inversion_clear H11.
rewrite <- H4.
unfold setA.
unfold setB.
intros.
destruct eq_nat_dec; destruct eq_var_dec; subst;
  inversion H11; inversion H13; subst...
rewrite shift_0_v.
  rewrite H9.
  split...
  split...
  unfold subst...
  f_equal.
  rewrite apply_with_offset_0_id.
  rewrite apply_with_offset_0_id.
  rewrite subst_trim_vars...  
destruct n; auto.
inversion e1; tauto.
apply H12 with (a := a0)...
    (* reduction *)
split.
clear IHAAS...
    (* closed*)
split...
    (* subst *)
split...
    (* heap_ok *)
unfold heapB_ok.
      (* heap_ok 1 *)
split...
unfold setB in H6.
destruct eq_nat_dec.
  inversion H6.
  subst.
  apply no_atoms_EES_no_atoms in H7...
  constructor...
  destruct H2.
  eauto.
destruct H10.
eapply H10...
apply H6.
      (* heap_ok 2 *)
unfold setB in H6.
destruct eq_nat_dec.
  subst.
  inversion H6.
  subst.
  constructor.
  clear IHAAS.
  simpl_arith.
  inversion H8; subst.
  constructor.
  apply closed_trim_vars...
destruct H10.
eapply H11.
apply H6.
    (* A (env_find) *)
apply subst_var_env_find...
inversion NOATOMS...
  (* premises of the IH *)
    (* closed_by_expr *)
inversion_clear H2.
set (lf := Lf Update 0 e).
assert (closed_by_lf (assoc_keys tau) 0 lf).
  eapply H8.
  apply H.
inversion_clear H2...
    (* subst *)
rewrite H6.
rewrite shift_0_v.
trivial.
    (* no_atoms *)
inversion_clear H2.
set (lf := Lf Update 0 e).
assert (no_atoms_lf lf).
  eapply H7.
  apply H.
inversion_clear H2...
    (* only_atoms *)
oa_inversion ONLYATOMS.
constructor...
eapply oa_heap_val; eauto.
(* [3] Case E_App5 *)
subst_inversion EQe.
dupl H.
apply similar_dom_atom with (GammaP := XiP) in H6...
destruct p; try contradiction...
similar_value H XiP.
rename e into etau.
rename x0 into e.
rename x1 into tau.
rewrite shift_0_v in H9.
eapply IHAAS1 with (a := e) (beta := tau) (XiP := XiP) in H2...
  (* thesis *)
destruct H2.
rename x0 into DeltaP.
destruct H2.
rename x0 into rho.
destruct H2 as [x0 []].
destruct H10.
destruct H11.
destruct H12.
subst_inversion H12.
destruct xs0; isa; try discriminate.
destruct xs;  isa; try discriminate.
dupl H0.
apply similar_dom_atom with (GammaP := DeltaP) in H9...
destruct q; try contradiction...
similar_value H0 DeltaP.
rename f into fmu.
rename x0 into f.
rename x2 into mu.
apply IHAAS2 with (a1 := App x1 nil) (beta := rho)
    (XiP := setB DeltaP a
      (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++
        shift (length qk) mu) (fv (Lf_n (n - length qk) f))))
  in H3...
  (* thesis *)
destruct H3.
rename x0 into OmegaP.
destruct H3.
rename x0 into xi.
destruct H3.
destruct H3.
destruct H17.
destruct H18.
destruct H19.
exists OmegaP.
exists xi.
exists x0.
    (* similar *)
split...
    (* reduction *)
split.
apply E_App5 with (p := a) (q := a0) (n := n) (Theta := OmegaP)
  (x := x) (pn := pn) (rs := rs) (nu := xi) (w := x0)
  (sigma := beta) (f := f) (mu := mu) in H10...
      (* env_find 1 *)
apply subst_var_env_find...
inversion NOATOMS...
      (* env_find 2 *)
apply subst_var_env_find...
apply no_atoms_EES_no_atoms in H10.
destruct H5.
inversion H10...
  set (lf := Lf Update 0 e).
  assert (no_atoms_lf lf).
    eapply H5.
    eauto.
inversion_clear H21...
apply H5.
    (* closed, subst and heap_ok *)
auto.
  (* premises of IHAAS2 *)
    (* subst *)
unfold subst...
rewrite apply_with_offset_0_v...
    (* no_atoms *)
apply no_atoms_EES_no_atoms in H10...
set (lf := Lf_u e).
assert (no_atoms_lf lf).
  destruct H5.
  eapply H5.
  eauto.
inversion_clear H17...
destruct H5.
eapply H5.
eauto.
    (* similar *)
      (* similar 1 *)
split.
intro.
unfold setA.
destruct eq_var_dec; try discriminate...
inversion_clear H2.
apply H17.
      (* similar 2 *)
split.
intro.
unfold setA.
unfold setB.
destruct eq_nat_dec; destruct eq_var_dec.
subst; split; intro; discriminate.
subst; destruct n0; auto.
inversion e0; tauto.
inversion_clear H2.
inversion_clear H18.
apply H2.
      (* similar 3 *)
inversion_clear H2.
inversion_clear H18.
unfold setA.
unfold setB.
intros.
destruct eq_nat_dec; destruct eq_var_dec; subst;
  inversion H18; inversion H20; subst.
split...
split...
apply only_atoms_EES_only_atoms in H10.
oa_inversion H10.
apply oa_accum_map in OA_ACCUM.
case OA_ACCUM.
intros x0 EQ.
rewrite -> EQ.
unfold Lf_n.
rewrite trim_fv.
rewrite shift_app_distr.
rewrite shift_cummulative.
rewrite <- EQ.
clear x0 EQ.
cutrewrite (n - length qk + length qk = n).
rewrite shift_zip_var_list.
cutrewrite (length qk + (n - length qk) = n)...
apply subst_lemma.
apply oa_heap_val with (Gamma := DeltaP) (p := a0) (lf := Lf_n n e0)...
omega.
omega.
omega.
omega.
clear IHAAS1.
clear IHAAS2.
unfold oa_heap in OA_HEAP.
unfold oa_env.
eapply OA_HEAP; eauto.
rewrite map_length; omega.
oa_inversion ONLYATOMS.
assert (oa_env tau).
  eapply oa_heap_val; eauto.
assert (only_atoms XiP beta nil).
  constructor; auto with oa.
apply only_atoms_EES_only_atoms in H10.
oa_inversion H10...
constructor; auto with oa.
constructor; auto with oa.
destruct n0; auto.
inversion e1; tauto.
apply H19 with (a := a1)...
    (* heap_ok *)
unfold heapB_ok.
      (* heap_ok 1 *)
split...
unfold setB in H17.
destruct eq_nat_dec.
  inversion H17.
  subst.
  inversion H13.
  set (lf := Lf_n n f).
  assert (no_atoms_lf lf).
    eapply H16.
    apply H0.
  inversion_clear H19.
  constructor...
inversion H13.
eapply H18...
eauto.
      (* heap_ok 2 *)
unfold setB in H17.
destruct eq_nat_dec.
        (* eq *)
inversion H17; subst.
clear IHAAS1 IHAAS2.
inversion H13; subst.
apply H18 in H0.
inversion H0; subst...
constructor...
apply closed_trim_fv.
apply closed_transfer...
omega.
        (* neq *)
inversion H13; subst.
eapply H19; eauto.
    (* only_atoms *)
oa_inversion ONLYATOMS.
assert (oa_env tau).
  eapply oa_heap_val; eauto.
assert (only_atoms XiP tau nil).
  constructor; auto with oa.
apply only_atoms_EES_only_atoms in H10...
oa_inversion H10.
constructor; auto with oa.
apply oa_setB...
apply oa_env_trim.
apply oa_env_app.
apply oa_env_zip_var_list...
  apply oa_env_shift.
  eapply oa_heap_val; eauto.
  (* premises of IHAAS1 *)
    (* closed_by_expr *)
inversion H5.
set (lf := Lf Update 0 e).
assert (closed_by_lf (assoc_keys tau) 0 lf).
  eapply H11.
  apply H.
inversion_clear H12...
    (* no_atoms *)
inversion H5.
set (lf := Lf Update 0 e).
assert (no_atoms_lf lf).
  eapply H10.
  apply H.
inversion_clear H12...
    (* only_atoms *)
oa_inversion ONLYATOMS.
constructor; auto with oa...
eapply oa_heap_val; eauto.
(* [2] Case Let *)
subst_inversion EQe.
apply atoms_exists in H0.
destruct H0.
rename x into ats0.
assert (length lfs = length lfs0).
  rewrite H6.
  rewrite map_length.
  trivial.
rename H5 into H9.
apply IHAAS with
    (XiP := allocB XiP ats0 (map
      (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats0)
        ++ shift (length lfs) beta) (fv lf))) lfs0))
    (a := e0)
    (beta := zip_var_list (length lfs0) (map Atom ats0) ++
      shift (length lfs0) beta)
  in H2...
  (* thesis *)
clear IHAAS.
destruct H2 as [x [x0 [x1 []]]].
destruct H5.
rename x into DeltaP.
rename w into wxi.
rename x1 into w.
rename x0 into xi.
exists DeltaP.
exists xi.
exists w.
    (* similar *)
split...
    (* reduction *)
rewrite H9 in H5.
apply E_Let in H5...
      (* length *)
rewrite H0 in H.
rewrite map_length in H.
rewrite H6 in H.
rewrite map_length in H.
trivial.
      (* freshness *)
rewrite H0 in H1.
destruct H3.
destruct H11.
apply H11 in H1.
apply H1.
apply in_map...
  (* premises of the IH *)
    (* closed_by_expr *)
inversion CBY; subst...
clear IHAAS H2.
assert (LEN : length lfs0 = length (map Atom ats0)).
  rewrite map_length in *.
  rewrite map_length in H.
  auto.
assert (ZER : 0 = length (map Atom ats0) - length (map Atom ats0)).
  omega.
rewrite LEN in *.
rewrite ZER.
apply closed_transfer...
  (* subst *)
rewrite H7.
oa_inversion ONLYATOMS.
rewrite subst_shift...
rewrite <- H0.
rewrite H9.
oa_inversion ONLYATOMS.
apply subst_lemma...
omega.
  (* no_atoms *)
inversion NOATOMS...
  (* similar *)
    (* similar 1 *)
split...
destruct (In_dec eq_var_dec (Index n) ats).
      (* in *)
rewrite H0 in i.
rewrite in_map_iff in i.
destruct i.
destruct H5.
discriminate.
      (* not in *)
rewrite allocA_nin...
inversion H3...
    (* similar 2 *)
split...
destruct (In_dec eq_nat_dec a ats0).
      (* in *)
rewrite H0.
dupl i.
eapply allocB_some with (H := XiP) in i.
destruct i.
rewrite H5; clear H5.
assert (In (Atom a) ats).
  rewrite H0.
  apply in_map...
eapply allocA_some with (H := Gamma) in H5.
destruct H5.
rewrite <- H0.
rewrite H5.
intuition; discriminate.
rewrite map_length...
rewrite map_length...
rewrite H0 in H.
rewrite map_length in H.
rewrite H6 in H.
rewrite map_length in H.
trivial.
      (* not in *)
inversion H3.
inversion H8.
rewrite allocA_nin...
rewrite allocB_nin...
rewrite H0.
intro.
apply in_map_iff in H12.
destruct H12.
destruct H12.
inversion H12.
rewrite H15 in H13.
tauto.
    (* similar 3 *)
subst.
oa_inversion ONLYATOMS.
rewrite map_length in *.
rewrite map_length in *.
eapply alloc_similar; eauto...
  (* heapB_ok *)
    (* no_atoms *)
split...
destruct (In_dec eq_nat_dec n ats0).
      (* in *)
apply allocB_in in H5...
apply in_map_iff in H5.
destruct H5.
destruct H5.
inversion H5.
inversion NOATOMS.
subst.
apply H14...
rewrite map_length.
subst.
rewrite map_length in H.
rewrite map_length in H...
      (* not in *)
rewrite allocB_nin in H5...
inversion H4.
eapply H8; eauto...
    (* closed_by *)
destruct (In_dec eq_nat_dec n ats0).
      (* in *)
apply allocB_in in H5.
apply in_map_iff in H5.
destruct H5.
destruct H5.
inversion CBY; subst.
clear IHAAS.
clear H2.
inversion H5; subst.
clear H5.
destruct lf.
constructor...
clear EQe.
clear CASE.
apply H12 in H8.
rewrite map_length.
inversion H8; subst.
assert (LEN : length lfs0 = length (map Atom ats0)).
  rewrite map_length in *.
  rewrite map_length in H.
  symmetry...
assert (B : b = length lfs0 + b - length lfs0).
  auto with arith.
apply closed_trim_fv.
rewrite B.
rewrite LEN.
apply closed_transfer; try omega...
rewrite <- LEN...
rewrite map_length.
rewrite H0 in H.
rewrite map_length in H.
rewrite H9 in H...
auto.
      (* not in *)
rewrite allocB_nin in H5...
destruct H4.
eapply H8; eauto.
  (* only_atoms *)
oa_inversion ONLYATOMS.
constructor.
    (* heap *)
unfold oa_heap...
destruct (In_dec eq_nat_dec v ats0).
      (* in *)
apply allocB_in in H5...
apply in_map_iff in H5.
destruct H5.
destruct H5.
inversion H5.
assert (oa_env tau).
  rewrite <- H13.
  apply oa_env_trim.
  apply oa_env_app; auto with oa.
  apply oa_env_zip_var_list.
  unfold oa_accum.
  apply atoms_map_atom.
unfold oa_env in H11.
eauto.
rewrite map_length.
rewrite H0 in H.
rewrite map_length in H.
rewrite H6 in H.
rewrite map_length in H...
      (* not in *)
rewrite allocB_nin in H5...
eauto with oa.
    (* env *)
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list.
unfold oa_accum.
apply atoms_map_atom.
    (* accum *)
auto.
(* [1] Case Case_of *)
subst_inversion EQe.
oa_inversion ONLYATOMS.
destruct (select_case_subst als als0 c c0 (length ps) e0 beta)...
destruct H.
rename x into e00.
apply IHAAS1 with (XiP := XiP) (beta := beta) (a := f) in H1...
  (* thesis *)
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H8.
rename x into DeltaP.
rename x0 into rho.
destruct H9.
destruct H10.
subst_inversion H10.
clear EQe.
apply IHAAS2 with (XiP := DeltaP) (beta0 := 
    zip_var_list (length ps) ps ++
    shift (length ps) beta)
  (a := e00) in H2...
    (* thesis *)
clear IHAAS1.
clear IHAAS2.
destruct H2.
destruct H2.
destruct H2.
rename x into ThetaP.
rename x0 into xi.
rename x1 into d.
destruct H2.
destruct H5.
exists ThetaP.
exists xi.
exists d.
destruct H6.
destruct H7.
      (* similar *)
split...
      (* reduction *)
split.
apply E_Case_of with (Delta := DeltaP) (e0 := e00) (rho := rho) (c := c)
  (c0 := c0) (ys := vs) (b := length ps) (rho_ys := ps)...
        (* length *)
unfold subst in H10; simpl in H10; inversion H10.
rewrite map_length...
        (* env_map *)
rewrite env_map_map_subst.
unfold subst in H10; simpl in H10; inversion H10.
rewrite apply_with_offset_0_id...
inversion NOATOMS; subst.
apply no_atoms_EES_no_atoms in H8...
inversion H8; subst.
inversion H8; subst...
destruct H4.
eapply H4; eauto.
inversion H9; subst...
      (*  closed_by, subst and heap_ok *)
split...
    (* premises of the second IH *)
      (* closed_by *)
clear CASE IHAAS1 IHAAS2.
inversion CBY; subst.
apply In_select_case in H.
apply H12 in H.
inversion H; subst...
assert (ZER : 0 = length ps - length ps); try omega.
rewrite ZER.
apply closed_transfer...
      (* subst*)
apply subst_lemma.
oa_inversion ONLYATOMS...
omega.
      (* no_atoms *)
inversion NOATOMS; subst.
apply In_select_case in H.
apply H12 in H.
inversion H; subst...
      (* only_atoms *)
oa_inversion ONLYATOMS.
clear IHAAS1.
clear IHAAS2.
apply only_atoms_EES_only_atoms in H8.
inversion H8; subst; constructor...
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list.
inversion H9; subst.
unfold subst in H10; simpl in H10.
rewrite apply_with_offset_0_id in H10.
inversion H10.
apply oa_accum_map_subst_var with (x := Atom 0)...
constructor; auto; constructor...
constructor; auto with oa.
  (* premises of the first IH *)
    (* closed_by *)
inversion CBY; subst...
    (* no_atoms *)
inversion NOATOMS; subst...
    (* only_atoms *)
oa_inversion ONLYATOMS.
constructor; auto with oa.
Qed.

(** * Soundness *)

Proposition EES_sound :
forall GammaP e beta rs OmegaP f xi qs
    (RED : ($ GammaP $ e $ beta $ rs ↓↓↓ OmegaP $ f $ xi $ qs))
    (Gamma : heapA)
    (NOATOMS : no_atoms e)
    (ONLYATOMS : only_atoms GammaP beta rs)
    (OK_GammaP : heapB_ok GammaP)
    (SIM_Gamma : similar Gamma GammaP)
    (CLOSED : closed_by_expr (assoc_keys beta) 0 e),
  exists Omega,
    ($ Gamma $ e~[beta] $ rs ↓↓ Omega $ f~[xi] $ qs) /\
    similar Omega OmegaP /\
    heapB_ok OmegaP /\
    closed_by_expr (assoc_keys xi) 0 f.
Proof with isa.
intros ? ? ? ? ? ? ? ? ?.
induction RED...
(* [8] Case Con *)
exists Gamma0.
split...
unfold subst...
(* [7] Case Accum *)
apply IHRED in SIM_Gamma...
destruct SIM_Gamma.
destruct H1.
exists x0.
split...
apply A_Accum.
destruct xm...
intro; discriminate.
unfold subst in H1...
rewrite apply_with_offset_0_v in *.
rewrite apply_with_offset_0_id in *.
apply map_subst_env_map in H0.
rewrite H0.
inversion NOATOMS; subst...
constructor...
inversion NOATOMS; subst...
constructor; isa; contradiction.
oa_inversion ONLYATOMS.
constructor...
apply oa_accum_app...
eapply oa_env_map; eauto.
inversion CLOSED; subst.
constructor...
constructor...
contradiction.
(* [6] Case App1 *)
exists Gamma0.
split...
apply env_find_subst_var in H.
unfold subst...
rewrite apply_with_offset_0_id.
rewrite H.
eapply similar_value_left in H0; eauto.
(* [5] Case App2_5 *)
assert (TAU : oa_env tau).
  oa_inversion ONLYATOMS.
  unfold oa_heap in OA_HEAP.
  unfold oa_env.
  eapply OA_HEAP; eauto.
assert (E : no_atoms e).
  destruct OK_GammaP.
  apply H2 in H0.
  inversion H0; subst...
assert (CLOSED_E : closed_by_expr
    (assoc_keys (zip_var_list m (firstn m pn) ++ shift m tau)) 0 e).
  destruct OK_GammaP.
  apply H3 in H0.
  inversion H0; subst...  
  cutrewrite (0 = m - m).
  assert (m = length (firstn m pn)).
    symmetry.
    apply firstn_le_length...
  rewrite H4 at 1 3 4 5.
  apply closed_transfer.
  trivial.
  rewrite <- H4...
  omega.
apply env_find_subst_var in H.
eapply similar_value_left in H0; eauto.
apply IHRED in SIM_Gamma...
destruct SIM_Gamma.
destruct H2.
exists x0.
split...
eapply A_App2_5; eauto.
clear IHRED.
rewrite apply_with_offset_0_id.
rewrite H.
apply H0.
rewrite subst_lemma...
rewrite firstn_length.
auto with arith.
oa_inversion ONLYATOMS.
constructor; auto with oa.
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list.
unfold oa_accum in *.
apply atoms_firstn...
(* [4] Case App4 *)
assert (TAU : oa_env tau).
  oa_inversion ONLYATOMS.
  unfold oa_heap in OA_HEAP.
  unfold oa_env.
  eapply OA_HEAP; eauto.
assert (E : no_atoms e).
  destruct OK_GammaP.
  apply H1 in H0.
  inversion H0; subst...
assert (CLOSED_E : closed_by_expr (assoc_keys tau) 0 e).
  destruct OK_GammaP.
  apply H2 in H0.
  inversion H0; subst...  
eapply similar_value_left in H0; eauto.
dupl SIM_Gamma.
apply IHRED in SIM_Gamma0...
destruct SIM_Gamma0.
exists (setA x0 (Atom p) (Lf_n 0 ((Constr C xs)~[rho]))).
unfold subst...
rewrite apply_with_offset_0_v.
rewrite apply_with_offset_0_id.
apply env_find_subst_var in H.
rewrite H.
split.
eapply A_App4; eauto.
rewrite shift_0_v.
destruct H1.
unfold subst in *...
rewrite apply_with_offset_0_id in *...
split.
  (* similar *)
unfold similar.
    (* similar 1 *)
split.
intro.
unfold setA.
destruct eq_var_dec; [ discriminate | ]...
destruct H1.
destruct H2.
inversion_clear H2.
apply H4.
      (* similar 2 *)
split.
intro.
unfold setA.
unfold setB.
destruct eq_nat_dec; destruct eq_var_dec.
subst; split; intro; discriminate.
subst; destruct n; auto.
inversion e0; tauto.
destruct H1.
destruct H2.
inversion_clear H2.
inversion_clear H5.
apply H2.
      (* similar 3 *)
destruct H1.
destruct H2.
inversion_clear H2.
inversion_clear H5.
unfold setA.
unfold setB.
intros.
destruct eq_nat_dec; destruct eq_var_dec; subst;
  inversion H5; inversion H7; subst...
rewrite shift_0_v; auto.
  split...
  split...
  unfold subst...
  rewrite apply_with_offset_0_id...
  f_equal.
  apply subst_trim_vars.
destruct n; auto.
inversion e1; tauto.
apply H6 with (a := a)...
  (* heap_ok *)
split.
destruct H1.
destruct H2.
unfold heapB_ok.
    (* heap_ok 1 *)
split...
unfold setB in H4.
destruct eq_nat_dec.
  inversion H4.
  subst.
  apply no_atoms_EES_no_atoms in RED...
  constructor...
  destruct OK_GammaP.
  eauto.
destruct H3.
eapply H3...
apply H4.
      (* heap_ok 2 *)
unfold setB in H4.
destruct eq_nat_dec.
  subst.
  inversion H4.
  subst.
  constructor.
  destruct H3...
  constructor.
  inversion H5; subst.
  apply closed_trim_vars...
destruct H3.
destruct H3.
eapply H6.
apply H4.
    (* closed_by *)
tauto.
  (* only_atoms *)
oa_inversion ONLYATOMS.
constructor...
(* [3] Case App5 *)
assert (TAU : oa_env tau).
  oa_inversion ONLYATOMS.
  unfold oa_heap in OA_HEAP.
  unfold oa_env.
  eapply OA_HEAP; eauto.
assert (CLOSED_E : closed_by_expr (assoc_keys tau) 0 e).
  destruct OK_GammaP.
  apply H5 in H1.
  inversion H1; subst...  
dupl SIM_Gamma.
apply IHRED1 in SIM_Gamma0...
destruct SIM_Gamma0.
destruct H4.
destruct H5.
destruct H6.
rename Delta into DeltaP.
rename x0 into Delta.
remember (f~[shift n mu]) as fmu.
apply IHRED2 with (Gamma := setA Delta (Atom p)
  (Lf_n (n - length qk) (fmu~[zip_var_list n qk]))) in H7.
destruct H7.
exists x0.
    (* red *)
split.
unfold subst...
rewrite apply_with_offset_0_v.
apply env_find_subst_var in H.
rewrite H.
remember (w~[nu]) as wnu.
dupl Heqwnu.
unfold subst in Heqwnu0.
rewrite <- Heqwnu0.
remember (e~[tau]) as etau.
unfold subst in H4...
rewrite apply_with_offset_0_v in H4.
apply env_find_subst_var in H0.
rewrite H0 in H4.
destruct H7.
apply A_App5 with (Delta := Delta) (q := Atom q) (qk := qk)
  (e := etau) (f := fmu) (n := n)...
      (* App *)
eapply similar_value_left in H1; eauto.
rewrite shift_0_v in H1.
subst...
      (* App *)
eapply similar_value_left in H2; eauto.
subst...
      (* App *)
assert (QQQ : App y nil ~ [rho] = App (Atom q) nil).
  unfold subst...
  rewrite apply_with_offset_0_v.
  rewrite H0...
rewrite QQQ in H7...
    (* similar *)
destruct H7.
destruct H8.
destruct H9...
  (* no atoms *)
unfold env_find in H0.
destruct y...
constructor.
constructor.
constructor...
contradiction.
discriminate.
  (* only atoms *)
oa_inversion ONLYATOMS.
apply only_atoms_EES_only_atoms in RED1.
oa_inversion RED1...
constructor...
    (* heap *)
unfold oa_heap...
unfold setB in H8.
destruct eq_nat_dec.
      (* eq *)
inversion H8; subst; clear H8.
apply In_trim in H9.
apply in_app_or in H9.
destruct H9.
apply In_zip_var_list in H8...
assert (OAMU : oa_env mu).
  unfold oa_heap in OA_HEAP0.
  unfold oa_env...
  eapply OA_HEAP0; eauto...
apply oa_env_shift with (m := length qk) in OAMU.
unfold oa_env in OAMU.
eapply OAMU; eauto.
      (* neq *)
assert (OATAU0 : oa_env tau0).
unfold oa_heap in OA_HEAP0.
unfold oa_env...
eapply OA_HEAP0; eauto...
unfold oa_env in OATAU0.
eapply OATAU0; eauto.
    (* accum *)
apply oa_accum_app...
constructor; auto with oa.
  (* heap_ok *)
unfold heapB_ok.
    (* heap_ok 1 *)
split...
unfold setB in H8.
destruct eq_nat_dec.
      (* eq *)
inversion H8; subst; clear H8.
destruct H6.
apply H6 in H2.
inversion H2; subst.
constructor...
      (* neq *)
destruct H6.
eapply H6; eauto.
    (* heap_ok 2 *)
unfold setB in H8.
destruct eq_nat_dec.
      (* eq *)
inversion H8; subst; clear H8.
destruct H6.
apply H8 in H2.
inversion H2; subst.
constructor...
apply closed_trim_fv.
apply closed_transfer...
omega.
      (* neq *)
destruct H6.
eapply H9; eauto.
  (* similar *)
unfold similar.
    (* similar 1 *)
split...
unfold setA.
destruct eq_var_dec.
discriminate.
destruct H5...
    (* similar 2 *)
split...
unfold setA.
unfold setB.
destruct eq_nat_dec; destruct eq_var_dec.
subst; split; intro; discriminate.
subst; destruct n0; auto.
inversion e0; tauto.
inversion_clear H5.
inversion_clear H9.
apply H5.
    (* similar 3 *)
inversion_clear H5.
inversion_clear H11.
unfold setA in *.
unfold setB in *.
destruct eq_nat_dec; destruct eq_var_dec; subst;
  inversion H8; inversion H9; subst...
split...
split...
  apply only_atoms_EES_only_atoms in RED1.
  oa_inversion RED1.
  apply oa_accum_map in OA_ACCUM.
  case OA_ACCUM.
  intros x0 EQ.
  rewrite -> EQ.
  unfold Lf_n.
  rewrite trim_fv.
  rewrite shift_app_distr.
  rewrite shift_cummulative.
  rewrite <- EQ.
  clear x0 EQ.
  cutrewrite (n - length qk + length qk = n).
  rewrite shift_zip_var_list.
  cutrewrite (length qk + (n - length qk) = n)...
  apply subst_lemma.
apply oa_heap_val with (Gamma := DeltaP) (p := q) (lf := Lf_n n e0)...
omega.
omega.
omega.
omega.
unfold oa_heap in OA_HEAP.
unfold oa_env.
eapply OA_HEAP; eauto.
rewrite map_length; omega.
oa_inversion ONLYATOMS.
assert (oa_env tau).
  eapply oa_heap_val; eauto.
assert (only_atoms Gamma sigma nil).
  constructor; auto with oa.
apply only_atoms_EES_only_atoms in RED1.
oa_inversion RED1...
constructor; auto with oa.
constructor; auto with oa.
destruct n0; auto.
inversion e1; tauto.
apply H12 with (a := a)...
  (* no atoms *)
destruct OK_GammaP.
apply H4 in H1.
inversion H1; subst...
  (* only atoms *)
oa_inversion ONLYATOMS.
constructor...
unfold oa_accum.
apply atoms_nil.
(* [2] Case Let *)
rename Gamma into GammaP.
rename Gamma0 into Gamma.
assert (NAE : no_atoms e).
  inversion NOATOMS...
apply IHRED with
    (Gamma := allocA Gamma (map Atom ats)
    (map (subst_lf (zip_var_list (length lfs) (map Atom ats) ++
      shift (length lfs) sigma)) lfs))
  in NAE.
destruct NAE.
rename Delta into DeltaP.
rename x into Delta.
exists Delta.
  (* thesis *)
oa_inversion ONLYATOMS.
destruct H1.
destruct H2.
destruct H3.
split...
remember (w~[rho]) as wrho.
unfold subst...
apply A_Let with (ats := map Atom ats).
    (* length *)
rewrite map_length.
rewrite map_length.
trivial.
    (* atoms *)
apply atoms_map_atom.
    (* freshness *)
intros.
clear IHRED.
destruct SIM_Gamma.
inversion H7.
assert (is_atom a).
  apply atom_in_map_atom with (ats := ats)...
to_atom a.
case H8 with (a := a)...
apply H12.
apply H0.
apply in_map_iff in H5.
destruct H5.
destruct H5.
inversion H5; subst...
    (* red *)
rewrite map_length.
rewrite subst_shift.
rewrite subst_lemma...
rewrite lf_subst_lemma in H1...
rewrite map_length.
rewrite <- H.
apply le_refl.
trivial.
  (* premises of the IH *)
    (* only atoms *)
oa_inversion ONLYATOMS.
constructor...
unfold oa_heap...
destruct (In_dec eq_nat_dec v ats).
      (* in *)
apply allocB_in in H1.
apply in_map_iff in H1.
destruct H1.
destruct H1.
inversion H1; subst; clear H1.
apply In_trim in H2.
apply in_app_or in H2.
destruct H2.
apply In_zip_var_list in H1.
apply in_map_iff in H1.
destruct H1.
destruct H1.
subst...
apply oa_env_shift with (m := length lfs) in OA_ENV...
unfold oa_env in OA_ENV.
eauto.
rewrite map_length...
auto.
      (* not in *)
rewrite allocB_nin in H1...
unfold oa_heap in OA_HEAP.
eapply OA_HEAP; eauto.
    (*  *)
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list; auto with oa.
unfold oa_accum.
apply atoms_map_atom.
    (* heap ok *)
unfold heapB_ok.
      (* heap ok 1 *)
split...
destruct (In_dec eq_nat_dec n ats).
        (* in *)
apply allocB_in in H1...
apply in_map_iff in H1.
destruct H1.
destruct H1.
inversion H1; subst; clear H1.
inversion NOATOMS; subst.
apply H4...
rewrite map_length...
        (* not in *)
rewrite allocB_nin in H1...
unfold heapB_ok in OK_GammaP.
destruct OK_GammaP.
eauto.
      (* heap ok 2 *)
destruct (In_dec eq_nat_dec n ats).
        (* in *)
apply allocB_in in H1...
apply in_map_iff in H1.
destruct H1.
destruct H1.
inversion H1; subst; clear H1.
inversion CLOSED; subst.
apply H4 in H2...
inversion H2; subst.
apply closed_transfer with (qk := map Atom ats) in H1.
constructor...
apply closed_trim_fv.
assert (L : length lfs + b - length (map Atom ats) = b).
  rewrite map_length.
  rewrite <- H.
  auto with arith.
rewrite L in H1.
cutrewrite (length lfs = length (map Atom ats))...
  rewrite map_length...
rewrite map_length...
rewrite <- H.
auto with arith.
rewrite map_length...
        (* not in *)
rewrite allocB_nin in H1...
unfold heapB_ok in OK_GammaP.
destruct OK_GammaP.
eauto.
    (* similar *)
unfold similar.
      (* similar 1 *)
split...
destruct (In_dec eq_var_dec (Index n) (map Atom ats))...
        (* in *)
apply in_map_iff in i.
destruct i.
destruct H1.
discriminate.
        (* not in *)
rewrite allocA_nin...
unfold similar in SIM_Gamma.
destruct SIM_Gamma...
      (* similar 2 *)
split...
destruct (In_dec eq_nat_dec a ats).
        (* in *)
dupl i.
eapply allocB_some with (H := GammaP) in i0.
destruct i0.
rewrite H1; clear H1.
dupl i.
apply in_map with (f := Atom) in i0.
eapply allocA_some with (H := Gamma) in i0.
destruct i0.
rewrite H1.
intuition; discriminate.
rewrite map_length.
rewrite map_length...
rewrite map_length...
        (* not in *)
inversion SIM_Gamma.
inversion H2.
rewrite allocA_nin...
rewrite allocB_nin...
intro.
apply in_map_iff in H5.
destruct H5.
destruct H5.
inversion H5.
rewrite H8 in H6.
tauto.
      (* similar 3 *)
oa_inversion ONLYATOMS.
eapply alloc_similar; eauto...
rewrite <- lf_subst_lemma...
    (* closed by *)
inversion CLOSED; subst.
rewrite plus_comm in H4.
apply closed_transfer with (qk := (map Atom ats)) in H4.
cutrewrite (0 = length lfs + 0 - length lfs); try omega.
rewrite assoc_keys_app_distr in *.
assert (length lfs = length (map Atom ats)).
  rewrite map_length...
rewrite H1 in *...
rewrite map_length in *.
rewrite <- H.
auto with arith.
(* [1] Case Case_of *)
dupl SIM_Gamma.
apply IHRED1 in SIM_Gamma0...
destruct SIM_Gamma0.
destruct H2.
destruct H3.
destruct H4.
clear IHRED1.
rename Delta into DeltaP.
rename x into Delta.
dupl H4.
apply IHRED2 with (Gamma := Delta) in H4...
destruct H4.
destruct H4.
destruct H7.
destruct H8.
clear IHRED2.
exists x.
split...
oa_inversion ONLYATOMS.
apply map_subst_env_map in H0.
apply select_case_subst_right with (beta := sigma) in H1...
assert (CYS : Constr c ys ~ [rho] = Constr c rho_ys).
  unfold subst...
  rewrite apply_with_offset_0_id.
  rewrite H0...
rewrite CYS in H2.
apply A_Case_of with (Delta := Delta) (b := b) (e0 := e0 ~ [shift b sigma])
  (c := c) (c0 := c0) (ps := rho_ys)...
  (* length *)
rewrite <- H0.
rewrite map_length...
  (* reduction *)
rewrite subst_lemma...
  (* length *)
rewrite <- H0.
rewrite map_length...
omega.
  (* no atoms in alt *)
clear IHRED2.
inversion NOATOMS; subst.
apply In_select_case in H1.
apply H10 in H1.
inversion H1; subst...
  (* only atoms *)
oa_inversion ONLYATOMS.
apply only_atoms_EES_only_atoms in RED1.
oa_inversion RED1.
constructor...
apply oa_env_app; auto with oa.
apply oa_env_zip_var_list.
eapply oa_env_map; eauto.
constructor; auto with oa.
  (* closed by *)
clear IHRED2.
inversion CLOSED; subst.
apply In_select_case in H1.
apply H10 in H1.
inversion H1; subst...
assert (LRHO : length ys = length rho_ys).
  apply map_subst_env_map in H0.
  rewrite <- H0.
  rewrite map_length...
cutrewrite (0 = length rho_ys - length rho_ys); try omega.
rewrite LRHO in *.
apply closed_transfer...
  (* no atoms *)
inversion NOATOMS; subst...
  (* only atoms *)
oa_inversion ONLYATOMS.
constructor; auto with oa.
  (* closed by *)
inversion CLOSED...
Qed.
