(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains the definition of the argument-accumulating
semantics and proof of its equivalence with the STG natural semantics. *)

Require Export Heaps.
Require Export Sem01.
Require Import Arith.Max.
Require Import Arith.Gt.
Require Import Wf_nat.

(** * Argument Accumulating Semantics *)

Reserved Notation "($ a $ b $ e ↓↓ c $ d $ f )"
  (at level 70, no associativity).

Inductive AAS : heapA -> expr -> vars -> heapA -> expr -> vars -> Prop :=

| A_Con : forall Gamma C pi,
  ($ Gamma $ Constr C pi $ nil ↓↓ Gamma $ Constr C pi $ nil) 

| A_Accum : forall Gamma Delta p pm qn w rs,
  pm <> nil ->
  ($ Gamma $ App p nil $ pm ++ qn ↓↓ Delta $ w $ rs) ->
  ($ Gamma $ App p pm  $ qn ↓↓ Delta $ w $ rs)

| A_App1 : forall Gamma p pn m e,
  Gamma p = Some (Lf_n m e) ->
  m > length pn ->
  ($ Gamma $ App p nil $ pn ↓↓ Gamma $ App p nil $ pn)

| A_App2_5 : forall Gamma Delta m e p pn w rs,
  Gamma p = Some (Lf_n m e) ->
  m <= length pn ->
  ($ Gamma $ e~[zip_var_list m (firstn m pn)] $ skipn m pn
    ↓↓ Delta $ w $ rs) ->
  ($ Gamma $ App p nil $ pn ↓↓ Delta $ w $ rs)

| A_App4 : forall Gamma Delta e p C qs,
  Gamma p = Some (Lf_u e) ->
  ($ Gamma $ e $ nil ↓↓ Delta $ Constr C qs $ nil) ->
  ($ Gamma $ App p nil $ nil
    ↓↓ setA Delta p (Lf_n 0 (Constr C qs)) $ Constr C qs $ nil)

| A_App5 : forall Gamma Delta Theta p pn q qk e f n w rs,
  Gamma p = Some (Lf_u e) ->
  Delta q = Some (Lf_n n f) ->
  length qk < n ->
  ($ Gamma $ e $ nil ↓↓ Delta $ App q nil $ qk) ->
  ($ setA Delta p (Lf_n (n - length qk) (f~[zip_var_list n qk])) $
    App q nil $ qk ++ pn ↓↓ Theta $ w $ rs) ->
  ($Gamma $ App p nil $ pn ↓↓ Theta $ w $ rs)

| A_Let : forall Gamma Delta lfs e w ats rs ss,
  length ats = length lfs ->
  are_atoms ats ->
  (forall a : var, In a ats -> Gamma a = None) -> 
  ($ allocA Gamma ats
      (map (subst_lf (zip_var_list (length lfs) ats)) lfs)
    $ e~[zip_var_list (length lfs) ats] $ rs
    ↓↓ Delta $ w $ ss) ->
  ($ Gamma $ Letrec lfs e $ rs ↓↓ Delta $ w $ ss)

| A_Case_of : forall Gamma Delta Theta b e e0 als w c c0 ps rs qs,
  length ps = b ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Gamma $ e $ nil ↓↓ Delta $ Constr c ps $ nil) ->
  ($ Delta $ e0~[zip_var_list b ps] $ qs ↓↓ Theta $ w $ rs) ->
  ($ Gamma $ Case e als $ qs ↓↓ Theta $ w $ rs)

where "($ a $ b $ e ↓↓ c $ d $ f )" := (AAS a b e c d f).

Hint Resolve A_Con A_Accum A_App1 A_App2_5 A_App4 A_App5 A_Let A_Case_of.

(** * Completeness *)

Proposition app_accum_right :
forall Gamma Delta p pm qn w rs,
  ($ Gamma $ App p nil $ pm ++ qn ↓↓ Delta $ w $ rs) ->
  ($ Gamma $ App p pm  $ qn ↓↓ Delta $ w $ rs).
Proof.
induction pm; isa.
constructor; intuition; try discriminate.
Qed.

Hint Resolve app_accum_right.

Proposition app_accum_left :
forall Gamma Delta p pm qn w rs,
  ($ Gamma $ App p pm  $ qn ↓↓ Delta $ w $ rs) ->
  ($ Gamma $ App p nil $ pm ++ qn ↓↓ Delta $ w $ rs).
Proof.
intros.
inversion H; isa; subst; intuition.
Qed.

Hint Resolve app_accum_left.

Proposition app_accum :
forall Gamma Delta p pm qn w rs,
  ($ Gamma $ App p nil $ pm ++ qn ↓↓ Delta $ w $ rs) <->
  ($ Gamma $ App p pm  $ qn ↓↓ Delta $ w $ rs).
Proof.
intros; split; auto.
Qed.

Proposition AAS_complete :
forall Xi Psi a b, ($ Xi $ a ↓ Psi $ b) ->
forall Omega c Cs Ds, ($ Psi $ b $ Ds ↓↓ Omega $ c $ Cs) ->
  ($ Xi $ a $ Ds ↓↓ Omega $ c $ Cs).
Proof with intuition; auto with arith; eauto.
intros Xi Psi a b ast.
induction ast; intros Omega cc Cs Ds astast; isa; subst...
(* Case App2 *)
apply IHast in astast.
remember_destruct pn;
[ rewrite <- X in *
| rewrite -> X in *;
    apply A_Accum; try intuition; try rewrite H1 in X; try discriminate ];
eapply A_App2_5...
simpl; rewrite app_length; omega.
rewrite firstn_length_app.
rewrite skipn_length_app...
(* Case App3 *)
apply -> app_accum.
eapply A_App2_5...
rewrite app_length...
rewrite skipn_app...
rewrite firstn_app...
apply IHast1.
apply -> app_accum.
rewrite <- app_ass...
(* Case App4 *)
inversion astast; subst...
(* Case App5 *)
apply app_accum_right.
eapply A_App5; eauto.
apply IHast1.
apply app_accum_right.
rewrite <- app_nil_end.
eapply A_App1...
rewrite <- app_ass...
Qed.

Lemma app_value_heap :
forall Delta e Xi x xs b,
  ($ Delta $ e ↓ Xi $ b) ->
  b = App x xs ->
  exists f, exists m, Xi x = Some (Lf Dont_update m f) /\ m > length xs.
Proof with isa.
intros.
induction H; try discriminate...
inversion H0; subst.
exists e.
exists m...
Qed.

Proposition AAS_complete2 :
forall Xi a,
  (forall x xs, ($ emptyA $ a ↓ Xi $ App x xs) -> ($ emptyA $ a $ nil ↓↓ Xi $ App x nil $ xs))
  /\
  (forall C xs, ($ emptyA $ a ↓ Xi $ Constr C xs) -> ($ emptyA $ a $ nil ↓↓ Xi $ Constr C xs $ nil)).
Proof with isa.
intros.
split.
(* left *)
intros.
apply AAS_complete with (Psi := Xi) (b := App x xs) (Omega := Xi)
  (c := App x nil) (Cs := xs) (Ds := nil) in H...
apply app_value_heap with (x := x) (xs := xs) in H...
destruct H as [f [m []]].
destruct xs.
  (* nil *)
eapply A_App1; eauto.
  (* cons *)
apply A_Accum.
discriminate.
rewrite <- app_nil_end.
eapply A_App1; eauto.
(* right *)
intros.
apply AAS_complete with (Psi := Xi) (b := Constr C xs) (Omega := Xi)
  (c := Constr C xs) (Cs := nil) (Ds := nil) in H...
Qed.


(** * Soundness *)

Proposition AAS_value :
forall Xi Omega Pn Rs b d,
  ($ Xi $ b $ Pn ↓↓ Omega $ d $ Rs) ->
  ((exists c, exists ps, d = Constr c ps /\ Rs = nil))
  \/ (exists p, exists ps, d = App p ps).
Proof.
intros.
induction H; eauto.
Qed.

Reserved Notation "($ a $ b $ e ↓↓ c $ d $ f ^^ n )"
  (at level 70, no associativity).

Inductive AASN : heapA -> expr -> vars -> heapA -> expr -> vars ->
  nat -> Prop :=

| A_ConN : forall Gamma C pi,
  ($ Gamma $ Constr C pi $ nil ↓↓ Gamma $ Constr C pi $ nil ^^ 0) 

| A_AccumN : forall Gamma Delta p pm qn w rs N,
  pm <> nil ->
  ($ Gamma $ App p nil $ pm ++ qn ↓↓ Delta $ w $ rs ^^ N) ->
  ($ Gamma $ App p pm  $ qn ↓↓ Delta $ w $ rs ^^ S N)

| A_App1N : forall Gamma p pn m e,
  Gamma p = Some (Lf_n m e) ->
  m > length pn ->
  ($ Gamma $ App p nil $ pn ↓↓ Gamma $ App p nil $ pn ^^ 0)

| A_App2_5N : forall Gamma Delta m e p pn w rs N,
  Gamma p = Some (Lf_n m e) ->
  m <= length pn ->
  ($ Gamma $ e~[zip_var_list m (firstn m pn)] $ skipn m pn
    ↓↓ Delta $ w $ rs ^^ N) ->
  ($ Gamma $ App p nil $ pn ↓↓ Delta $ w $ rs ^^ S N)

| A_App4N : forall Gamma Delta e p C qs N,
  Gamma p = Some (Lf_u e) ->
  ($ Gamma $ e $ nil ↓↓ Delta $ Constr C qs $ nil ^^ N) ->
  ($ Gamma $ App p nil $ nil
    ↓↓ setA Delta p (Lf_n 0 (Constr C qs)) $ Constr C qs $ nil ^^ S N)

| A_App5N : forall Gamma Delta Theta p pn q qk e f n w rs M N,
  Gamma p = Some (Lf_u e) ->
  Delta q = Some (Lf_n n f) ->
  length qk < n ->
  ($ Gamma $ e $ nil ↓↓ Delta $ App q nil $ qk ^^ N) ->
  ($ setA Delta p (Lf_n (n - length qk) (f~[zip_var_list n qk])) $
    App q nil $ qk ++ pn ↓↓ Theta $ w $ rs ^^ M) ->
  ($ Gamma $ App p nil $ pn ↓↓ Theta $ w $ rs ^^ S (max M N))

| A_LetN : forall Gamma Delta lfs e w ats rs ss N,
  length ats = length lfs ->
  are_atoms ats ->
  (forall a : var, In a ats -> Gamma a = None) -> 
  ($ allocA Gamma ats
      (map (subst_lf (zip_var_list (length lfs) ats)) lfs)
    $ e~[zip_var_list (length lfs) ats] $ rs
    ↓↓ Delta $ w $ ss ^^ N) ->
  ($ Gamma $ Letrec lfs e $ rs ↓↓ Delta $ w $ ss ^^ S N)

| A_Case_ofN : forall Gamma Delta Theta b e e0 als w c c0 ps rs qs N M,
  length ps = b ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Gamma $ e $ nil ↓↓ Delta $ Constr c ps $ nil ^^ N) ->
  ($ Delta $ e0~[zip_var_list b ps] $ qs ↓↓ Theta $ w $ rs ^^ M) ->
  ($ Gamma $ Case e als $ qs ↓↓ Theta $ w $ rs ^^ S (max M N))

where "($ a $ b $ e ↓↓ c $ d $ f ^^ n )" := (AASN a b e c d f n ).

Ltac caseA x := case x; isa.

Lemma aasn_complete :
forall Gamma e ps Delta w qs,
  ($ Gamma $ e $ ps ↓↓ Delta $ w $ qs) ->
  exists N, ($ Gamma $ e $ ps ↓↓ Delta $ w $ qs ^^ N).
Proof with eauto.
intros.
induction H.
exists 0; constructor.
caseA IHAAS; exists (S x); constructor...
exists 0; econstructor...
caseA IHAAS; exists (S x); eapply A_App2_5N...
caseA IHAAS; exists (S x); eapply A_App4N...
caseA IHAAS1; caseA IHAAS2; exists (S (max x0 x)); eapply A_App5N...
caseA IHAAS; exists (S x); eapply A_LetN...
caseA IHAAS1; caseA IHAAS2; exists (S (max x0 x)); eapply A_Case_ofN...
Qed.

Lemma aasn_sound :
forall Gamma e ps Delta w qs N,
  ($ Gamma $ e $ ps ↓↓ Delta $ w $ qs ^^ N) ->
  ($ Gamma $ e $ ps ↓↓ Delta $ w $ qs).
Proof.
intros.
induction H; eauto.
Qed.

Proposition AAS_split :
forall N (Xi Psi Omega : heapA) (b c d : expr) (Rs Pt Ptn Qs : vars),
  ($ Xi $ b $ Pt ++ Ptn ↓↓ Omega $ d $ Rs ^^ N) ->
  exists Psi, exists c, exists Qs, exists N0, exists N1,
  ($ Xi $ b $ Pt ↓↓ Psi $ c $ Qs ^^ N0) /\
  ($ Psi $ c $ Qs ++ Ptn ↓↓ Omega $ d $ Rs ^^ N1) /\
  N0 <= N /\ N1 <= N.
Proof with try split; try omega; simpl; auto.
intro N.
induction N using lt_wf_ind; isa.
destruct N;
  inversion H0; subst;
  try (rewrite <- plus_n_Sm in *; discriminate).
(* Case *)
rewrite <- H4 in *.
exists Omega.
exists (Constr C pi).
exists nil.
exists 0.
exists 0.
symmetry in H4.
apply app_eq_nil in H4.
inversion_clear H4...
rewrite H1...
split...
rewrite H2...
(* Case *)
exists Omega.
exists (App p nil).
exists Pt.
exists 0.
exists 0...
eapply A_App1N; eauto.
rewrite app_length in H2...
(* Case *)
dupl_apply Xi H; auto.
destruct H1 as [x [x0 [x1 [x2 [x3 [H H1]]]]]].
destruct H1 as [H1 []].
exists x.
exists x0.
exists x1.
exists (S x2).
exists x3.
split.
apply A_AccumN...
apply H.
split...
apply H1...
rewrite app_ass...
(* Case *)
caseA (le_lt_dec m (length Pt)).
  (* m <= length Pt *)
rewrite firstn_app in *...
rewrite skipn_app in *...
dupl_apply H10 H...
destruct H1 as [x [x0 [x1 [x2 [x3 [H H1]]]]]].
destruct H1 as [H1 []].
apply A_App2_5N with (p := p) in H...
exists x.
exists x0.
exists x1.
exists (S x2).
exists x3.
split...
  (* length Pt < m *)
exists Xi.
exists (App p nil).
exists Pt.
exists 0.
exists (S N).
split.
eapply A_App1N; eauto.
split; intuition.
(* Case *)
symmetry in H1.
apply app_eq_nil in H1.
inversion_clear H1.
subst.
simpl in H0.
exists (setA Delta p (Lf_n 0 (Constr C qs))).
exists (Constr C qs).
exists nil.
exists (S N).
exists 0.
split...
simpl.
apply A_ConN.
intuition.
(* Case *)
rewrite <- app_ass in H12.
dupl_apply H12 H...
destruct H1 as [x [x0 [x1 [x2 [x3 [H H1]]]]]].
destruct H1 as [H1 []].
exists x.
exists x0.
exists x1.
exists (S (max x2 N0)).
exists x3.
split.
eapply A_App5N.
apply H2.
apply H3.
apply H4.
apply H5.
apply H.
split.
apply H1.
split.
apply le_n_S.
destruct (max_dec x2 N0); apply max_c_inv_to_le; auto.
  eapply le_trans.
  apply H7.
  eapply le_trans.
  eapply le_max_l.
  apply le_n_Sn.
    eapply le_lt_trans.
    apply le_max_l.
    apply lt_n_Sn.
(* Case Let *)
dupl_apply H11 H...
destruct H1 as [x [x0 [x1 [x2 [x3 [H H1]]]]]].
destruct H1 as [H1 []].
exists x.
exists x0.
exists x1.
exists (S x2).
exists x3.
split.
eapply A_LetN.
eauto.
auto.
eauto.
eauto.
split...
(* Case Case *)
dupl_apply H11 H...
destruct H1 as [x [x0 [x1 [x2 [x3 [H H1]]]]]].
destruct H1 as [H1 []].
exists x.
exists x0.
exists x1.
exists (S (max x2 N0)).
exists x3.
split.
eapply A_Case_ofN.
instantiate (2 := ps); eauto.
instantiate (1 := e0).
instantiate (1 := c1).
instantiate (1 := c0).
rewrite <- plus_n_O...
apply H4.
rewrite <- plus_n_O...
split.
apply H1.
split.
apply le_n_S.
apply max_c_inv_to_le; isa.
apply le_trans with (m := M)...
rewrite max_SS.
apply le_trans with (m := S M)...
auto with arith.
auto with arith.
Qed.

Fixpoint join_expr (Ds : list atom) (e : expr) {struct e} :
  expr :=
match e with
| App v vs => App v (vs ++ map Atom Ds)
| Constr c vs => Constr c vs
| Letrec dfs f => Letrec dfs (join_expr Ds f)
| Case e als => Case e (map (join_alt Ds) als)
end
with join_alt (Ds : list atom) (a : alt)
  {struct a} : alt :=
match a with
| Alt c b f => Alt c b (join_expr Ds f)
end.

Notation " e >< d " := (join_expr d e) (at level 70).
Notation " e ><' d " := (join_alt d e) (at level 70).

Proposition join_nil :
forall (e : expr), e >< nil = e.
Proof with isa.
induction e using expr_ind2 with
  (P1 := fun (lf : lambda_form) => True)
  (P2 := fun (al : alt) => al ><' nil = al)...
rewrite <- app_nil_end...
rewrite IHe...
f_equal; induction als; isa; f_equal...
rewrite IHe...
Qed.

Lemma closed_AAS_atoms :
forall N Xi Omega e f ps ds,
  (forall s lf, Xi s = Some lf -> closed_lf 0 lf) ->
  closed_expr 0 e ->
  ($ Xi $ e $ ps ↓↓ Omega $ f $ ds ^^ N) -> are_atoms ps ->
  are_atoms ds /\ closed_expr 0 f /\
  (forall s lf, Omega s = Some lf -> closed_lf 0 lf).
Proof with isa; eauto.
intro NN.
intros Xi Omega e f ps ds H J X A.
induction X...
(* Case *)
dupl J.
apply atoms_closed_app in J.
inversion_clear J...
(* Case *)
apply IHX...
eapply open_inv_to_closed.
  apply atoms_firstn...
  rewrite firstn_length.
  auto with arith.
apply H with (s := p).
apply H0.
  unfold are_atoms in *.
  intros.
  intuition.
  apply A.
  eapply In_skipn.
  apply H2.
(* Case *)
assert (closed_lf 0 (Lf_u e))...
inversion H1; subst...
ecase IHX...
destruct H4.
split...
split...
unfold setA in *.
destruct eq_var_dec...
inversion H6.
constructor...
(* Case *)
assert (closed_expr 0 e).
  apply H in H0; inversion H0; subst...
case IHX1...
unfold are_atoms; isa; contradiction.
destruct H5.
apply IHX2...
unfold setA in *.
destruct eq_var_dec...
inversion H7.
constructor...
eapply open_inv_to_closed0.
apply H4.
intuition.
case H6 with (s := q) (lf := Lf_n n f)...
(* Case *)
inversion J; subst...
case IHX...
destruct (In_dec eq_var_dec s ats).
  (* in *)
apply allocA_in in H3; auto.
apply in_map_iff in H3.
destruct H3.
rename x into lf0.
destruct H3.
assert (closed_lf (length lfs) lf0).
  apply H5; auto.
subst.
destruct lf0.
inversion_clear H7.
constructor; simpl.
fold map_expr.
rewrite <- H0 in *.
eapply open_inv_to_closed2...
rewrite map_length...
  (* not in *)
rewrite allocA_nin in H3; auto.
eapply H; auto.
apply H3.
apply open_inv_to_closed1...
(* Case *)
inversion J; subst.
assert (closed_expr 0 e).
  apply H4.
case IHX1...
unfold are_atoms; isa; contradiction.
destruct H3.
apply IHX2...
eapply open_inv_to_closed...
apply atoms_closed_constr in H3...
instantiate (1 := Update).
constructor...
assert (XX : closed_by_alt nil 0 (Alt c0 (length ps) e0))...
  apply H5.
  eapply In_select_case.
  apply H1.
inversion XX; subst...
Qed.

Lemma join_open :
forall Ds xs e, (e >< Ds)~[xs] = (e~[xs] >< Ds).
Proof with isa; intuition.
intros Ds xs.
assert (forall e n,
   map_expr (subst_var xs) n (e >< Ds) =
  (map_expr (subst_var xs) n  e >< Ds)).
  intro e.
  induction e using expr_ind2 with
  (P1 := fun (lf : lambda_form) => True)
  (P2 := fun (al : alt) => forall n,
     map_alt (subst_var xs) n (al ><' Ds) =
    (map_alt (subst_var xs) n  al ><' Ds))...
  (* Case App *)
  f_equal.
  induction vs...
  induction Ds...
  f_equal...
  f_equal...
  (* Case Letrec *)
  f_equal...
  (* Case Case *)
  f_equal.
  induction als...
  f_equal...
  (* Case Alt *)
  f_equal...
intro.
apply H with (n := 0).
Qed.

Lemma AAS_value_lemma :
forall Xi Omega b c ps qs N,
  ($ Xi $ b $ ps ↓↓ Omega $ c $ qs ^^ N) -> is_value c.
Proof with isa.
intros.
induction H...
Qed.

Proposition AAS_sound :
forall (N : nat) Xi Omega b c Ds Cs,
  (forall s lf, Xi s = Some lf -> closed_lf 0 lf) ->
  closed_expr 0 b ->
  ($ Xi $ b $ map Atom Ds ↓↓ Omega $ c $ map Atom Cs ^^ N) ->
  ($ Xi $ b >< Ds ↓ Omega $ c >< Cs).
Proof with intros; auto with arith.
intro N.
induction N using lt_wf_ind; isa.
destruct N;
  inversion H2; subst;
  try (rewrite <- plus_n_Sm in *; discriminate).
(* Case *)
isa.
(* Case *)
inversion H2; subst.
apply atoms_map_injection in H6.
subst.
eapply App1; simpl.
apply H8.
apply H12.
(* Case *)
dupl H11.
apply closed_AAS_atoms in H3...
destruct H3.
destruct H5.
dupl H1.
apply closed_0_args in H1.
apply atoms_exists in H1.
destruct H1.
rewrite H1 in *.
simpl.
rewrite <- map_app in *.
apply H in H11...
apply H0 with (s := s)...
eapply closed_rem_args; apply H7.
apply H0 with (s := s)...
eapply closed_rem_args; apply H1.
apply closed_0_args in H1.
apply atoms_app...
unfold are_atoms...
apply in_map_iff in H5.
destruct H5.
destruct H5.
unfold is_atom.
destruct a...
discriminate.
(* Case *)
caseA (le_lt_dec (length Ds) m).
  (* subcase eq *) 
eapply App2.
apply H4.
rewrite map_length in *.
apply le_antisym...
assert (QQ : forall xs, e~[xs] = (e~[xs] >< nil)).
  intro.
  symmetry.
  apply join_nil.
rewrite QQ.
eapply H.
Focus 4.
rewrite firstn_length_eq_id in H12.
rewrite skipn_length_eq_nil in H12.
simpl.
apply H12.
rewrite map_length in *.
apply le_antisym...
rewrite map_length in *.
apply le_antisym...
omega.
auto.
eapply open_inv_to_closed.
apply atoms_map_atom.
rewrite map_length in *.
apply le_antisym...
instantiate (1 := Dont_update).
apply H0 with (s := p)...
  (* subcase lt *)
assert (m < length Ds)...
replace (skipn m (map Atom Ds)) with (nil ++ skipn m (map Atom Ds))
  in H12...
apply AAS_split in H12; (try exact nil)...
destruct H12.
destruct H6.
destruct H6.
destruct H6.
destruct H6.
destruct H6.
destruct H7.
destruct H8.
dupl H6.
apply closed_AAS_atoms in H10; auto.
Focus 2.
eapply open_inv_to_closed.
  rewrite firstn_map.
  apply atoms_map_atom. 
  erewrite <- map_length in l.
  apply firstn_lt_length.
  apply l.
instantiate (1 := Dont_update).
apply H0 with (s := p)...
destruct H10.
destruct H11.
apply atoms_exists in H10.
destruct H10.
rewrite H10 in H6.
replace (nil (A := var)) with (map Atom nil) in H6...
dupl H6.
apply H in H6...
rewrite skipn_map in H7.
rewrite H10 in H7.
rewrite <- map_app in H7.
dupl H7.
rename H14 into HHH.
apply H in H7...
assert (is_value x0).
  eapply AAS_value_lemma; eauto.
inversion H14.
  subst.
simpl in *.
eapply App3.
apply H4.
rewrite map_length...
rewrite join_nil in H6; apply H6.
rewrite app_ass; rewrite skipn_map; rewrite <- map_app; auto.
  subst.
inversion HHH; subst.
apply skipn_lt_length_nil in H3.
rewrite map_app in H18.
assert (XX : map Atom x4 = nil).
  symmetry in H18.
  apply app_eq_nil in H18.
  destruct H18.
  auto.
rewrite XX in H18.
simpl in H18.
assert (nil = skipn m Ds).
  induction (skipn m Ds).
intuition.
simpl in *; discriminate.
intuition.
apply H12 with (s := s)...
apply H0 with (s := s)...
eapply open_inv_to_closed.
rewrite firstn_map.
apply atoms_map_atom.
rewrite firstn_lt_length...
rewrite map_length...
instantiate (1 := Dont_update).
apply H0 with (s := p)...
unfold are_atoms.
intuition.
inversion H11.
(* Case *)
simpl.
rewrite <- H3.
eapply App4.
apply H10.
rewrite <- join_nil.
rewrite <- join_nil with (e := e).
eapply H.
instantiate (1 := N).
omega.
apply H0.
rewrite <- empty_subst.
assert (QQ : forall m, zip_var_list m nil = nil).
  intros.
  simpl...
rewrite <- QQ with (m := 0).
eapply open_inv_to_closed...
apply atoms_nil.
instantiate (1 := Update).
apply H0 with (s := p)...
auto.
(* Case *)
dupl H7.
apply closed_AAS_atoms in H3.
destruct H3.
apply atoms_exists in H3.
destruct H3.
rewrite H3 in *.
rewrite <- map_app in H14.
apply H in H14.
assert (nil = map Atom nil).
  isa.
rewrite H9 in H7.
apply H in H7.
eapply App5.
apply H4.
apply H5.
apply H6.
  rewrite join_nil in H7.
  simpl in *.
apply H7.
  simpl.
  rewrite <- map_app.
apply H14.
auto with arith.
auto.
rewrite <- empty_subst.
assert (QQ : forall m, zip_var_list m nil = nil).
  intros.
  simpl...
rewrite <- QQ with (m := 0).
eapply open_inv_to_closed...
apply atoms_nil.
eapply H0.
apply H4.
auto with arith.
destruct H8.
isa.
destruct (eq_var_dec p s).
subst.
rewrite setA_eq in H10.
inversion H10.
constructor.
simpl.
eapply open_inv_to_closed0.
apply atoms_map_atom.
intuition.
instantiate (1 := Dont_update).
eapply H9.
apply H5.
rewrite setA_neq in H10.
eapply H9; apply H10.
auto.
tauto.
trivial.
rewrite <- empty_subst.
assert (QQ : forall m, zip_var_list m nil = nil).
  intros.
  simpl...
rewrite <- QQ with (m := 0).
eapply open_inv_to_closed...
apply atoms_nil.
eapply H0.
apply H4.
unfold are_atoms...
contradiction.
(* Case *)
eapply Let.
apply H4.
apply H5.
apply H6.
fold join_expr.
rewrite join_open.
eapply H.
instantiate (1 := N).
omega.
isa.
destruct (In_dec eq_var_dec s ats).
  (* subcase in *)
apply allocA_in in H3; auto.
apply in_map_iff in H3.
destruct H3.
rename x into lf0.
destruct H3.
assert (closed_lf (length lfs) lf0).
  inversion H1.
  subst.
  simpl in *.
  apply H10; auto.
subst.
destruct lf0.
inversion_clear H8.
constructor.
simpl.
fold map_expr.
rewrite <- H4 in *.
eapply open_inv_to_closed2...
rewrite map_length.
auto.
  (* subcase not in *)
rewrite allocA_nin in H3.
eapply H0.
apply H3.
apply n.
inversion H1; subst; isa.
apply open_inv_to_closed1; isa.
apply H13.
(* Case *)
dupl H6.
rename H3 into AAA.
apply closed_AAS_atoms in AAA...
assert (nil = map Atom nil).
  isa.
rewrite H3 in H6.
apply H in H6.
apply H in H13.
simpl in *.
eapply Case_of.
Focus 3.
rewrite join_nil in H6.
apply H6.
Focus 3.
instantiate (1 := e0 >< Ds).
instantiate (1 := length ps).
inversion H1; subst.
clear H3.
assert (In (Alt c1 (length ps) e0) als).
  eapply In_select_case.
  apply H5.
assert (closed_alt 0 (Alt c1 (length ps) e0)).
  apply H9...
inversion H4; subst; simpl in *.
assert (QWE : forall e Ds ps, closed_expr (length ps) e ->
  (e >< Ds)~[zip_var_list (length ps) ps] = 
  ((e~[zip_var_list (length ps) ps]) >< Ds)).
  intros.
  apply join_open.
rewrite QWE...
auto.
instantiate (1 := c1).
clear H6 H1 H2 H13 AAA.
induction als.
simpl in *.
discriminate H5.
destruct a.
destruct (eq_nat_dec c0 c2).
subst.
simpl in H5 |- *.
destruct eq_nat_dec.
f_equal.
inversion H5.
subst.
f_equal.
destruct n...
simpl in H5 |- *.
destruct (eq_nat_dec c0 c2) in H5 |- *.
subst.
destruct n...
apply IHals.
apply H5.
auto with arith.
tauto.
intuition.
inversion H1; subst.
assert (In (Alt c1 (length ps) e0) als).
  eapply In_select_case.
  apply H5.
assert (BBB : closed_alt 0 (Alt c1 (length ps) e0)).
  apply H12.
  auto.
inversion BBB; subst.
simpl in *.
apply open_inv_to_closed1...
apply atoms_closed_constr in H8...
auto with arith.
trivial.
inversion H1...
apply H0 with (s := s)...
inversion H1...
unfold are_atoms.
intuition.
inversion H3.
Qed.

Proposition AAS_sound2 :
forall b c Omega Cs,
  closed_expr 0 b ->
  ($ emptyA $ b $ nil ↓↓ Omega $ c $ map Atom Cs) ->
  ($ emptyA $ b ↓ Omega $ c >< Cs).
Proof with isa.
intros.
assert (BNIL : (b >< nil) = b).
  apply join_nil.
rewrite <- BNIL.
dupl H0.
apply aasn_complete in H0.
destruct H0.
apply AAS_sound with (N := x)...
unfold emptyA in H1; discriminate.
Qed.
