(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains the definition of the STG machine
and final proofs of completeness and soundness w.r.t. to STG natural
semantics. *)

Require Export Sem06.

(** * The STG Machine *)

(** We denote the STG machine rules using maybe unusual direction
of the arrow: we write [Config2 <-- Config1], so in the source code
the Config2 is written above Config1, just as in the DCPS semantics. *) 

Reserved Notation "($ x $ a $ b $ g $ e $ s <-- x0 $ a0 $ b0 $ g0 $ e0 $ s0 )"
  (at level 70, no associativity).

Inductive STG : instruction -> heapB -> expr -> env -> vars -> stack
             -> instruction -> heapB -> expr -> env -> vars -> stack
             -> Prop :=

| STG_Con : forall Gamma C pi sigma Ss,
  ($ ReturnCon $ Gamma $ Constr C pi $ sigma $ nil $ Ss <--
     Eval      $ Gamma $ Constr C pi $ sigma $ nil $ Ss)

| STG_Accum : forall Gamma x xm sigma_xm qn sigma Ss,
  env_map sigma xm = Some sigma_xm ->
  ($ Enter $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss <--
     Eval  $ Gamma $ App x xm  $ sigma $ qn             $ Ss)

| STG_App2_5 : forall Gamma m e x tau p pn sigma Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ Eval  $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss <--
     Enter $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss)

| STGA_App4 : forall Delta rho C xs p Ss,
  ($ ReturnCon $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss <--
     ReturnCon $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss)

| STGE_App4_5 : forall Gamma x p e tau sigma rs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ Eval  $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss <--
     Enter $ Gamma $ App x nil $ sigma $ rs $ Ss)

| STGA_App5 : forall Delta x p pn y q qk f n sigma rho mu Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ Enter $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss <--
     Enter $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss)

| STG_Let : forall Gamma sigma lfs e (ats : list nat) rs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ Eval $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    <--
    Eval $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss)

| STGE_Case_of : forall Gamma e als qs sigma Ss,
  ($ Eval $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss <--
     Eval $ Gamma $ Case e als $ sigma $ qs $ Ss)

| STGA_Case_of : forall Delta b e0 als ys c c0 rho_ys qs sigma rho Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Eval $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss <--
     ReturnCon $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss) 

where "($ x $ a $ b $ g $ e $ s <-- x0 $ a0 $ b0 $ g0 $ e0 $ s0 )" :=
  (STG x a b g e s x0 a0 b0 g0 e0 s0).

Hint Constructors STG.

(** * The STG Machine run *)

Reserved Notation "($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 -*-> a $ b $ g $ e )"
  (at level 70, no associativity).

Inductive STG_run : instruction -> heapB -> expr -> env -> vars -> stack
                                -> heapB -> expr -> env -> vars
                                -> Prop :=

| STG_Halt : forall Gamma w sigma ps,
  ($ ReturnCon $ Gamma $ w $ sigma $ ps $ nil -*-> Gamma $ w $ sigma $ ps)

| STG_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ Enter $ Gamma $ App x nil $ sigma $ pn $ nil -*-> Gamma $ App x nil $ sigma $ pn)

| STG_Step : forall x0 x1 h0 h1 e0 e1 g0 g1 a0 a1 s0 s1 h e g a,
  ($ x1 $ h1 $ e1 $ g1 $ a1 $ s1 <-- x0 $ h0 $ e0 $ g0 $ a0 $ s0) ->
  ($ x1 $ h1 $ e1 $ g1 $ a1 $ s1 -*-> h $ e $ g $ a ) ->
  ($ x0 $ h0 $ e0 $ g0 $ a0 $ s0 -*-> h $ e $ g $ a )

where "($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 -*-> a $ b $ g $ e )" :=
  (STG_run x0 a0 b0 g0 e0 s0 a b g e).

Hint Constructors STG_run.

Lemma STG_run_complete:
forall x0 a0 b0 g0 e0 s0 a b g e,
  ($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 ^^^  a $ b $ g $ e) ->
  ($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 -*-> a $ b $ g $ e).
Proof with eisa.
intros.
induction H; try eapply STG_Halt; try eapply STG_App1;
  try eapply STG_Step; eauto...
Qed.

Lemma STG_run_sound:
forall x0 a0 b0 g0 e0 s0 a b g e,
  ($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 -*-> a $ b $ g $ e) ->
  ($ x0 $ a0 $ b0 $ g0 $ e0 $ s0 ^^^  a $ b $ g $ e).
Proof with eisa.
intros.
induction H...
inversion H; subst...
Qed.


(** * Soundness and completeness of the STG machine *)

Proposition values :
forall Gamma e Delta f,
  ($ Gamma $ e ↓ Delta $ f) ->
(exists x, exists xs, f = App x xs) \/
(exists C, exists xs, f = Constr C xs).
Proof with isa.
intros.
induction H...
right; exists C; exists vs...
left; exists p; exists pn...
Qed.

Proposition completeness :
forall e x xs C Delta,
    closed_expr 0 e ->
    no_atoms e ->
(($ emptyA $ e ↓ Delta $ App x xs) ->
    exists DeltaP, exists y, exists sigma,
       ($ Eval $ emptyB $ e $ nil $ nil $ nil -*-> DeltaP $ App y nil $ sigma $ xs) /\
       similar Delta DeltaP /\
       App y nil ~ [sigma] = App x nil)
/\
(($ emptyA $ e ↓ Delta $ Constr C xs) ->
    exists DeltaP, exists ys, exists sigma,
       ($ Eval $ emptyB $ e $ nil $ nil $ nil -*-> DeltaP $ Constr C ys $ sigma $ nil) /\
       similar Delta DeltaP /\
       Constr C ys ~ [sigma] = Constr C xs).
Proof with isa.
intros.
split...
(* left *)
assert (H2 : ($emptyA $ e ↓ Delta $ App x xs))...
apply values in H1.
destruct H1 as [[x0 [xs0]] | [C0 [xs0]]].
(* left *)
inversion H1; subst...
dupl H2.
rename H3 into W1.
rename x0 into x.
rename xs0 into xs.
apply app_value_heap with (x := x) (xs := xs) in W1.
destruct W1 as [f [m [W1 W2]]].
(* sfsg *)
apply AAS_complete2 in H2.
apply EES_complete with (a := e) (beta := nil) (XiP := emptyB) in H2...
  (* *)
destruct H2 as [DeltaP [sigma [w [? [? [? []]]]]]].
exists DeltaP.
subst_inversion H5.
assert (xs0 = nil).
  destruct xs0...
  discriminate.
subst.
exists x0.
exists sigma.
split.
apply EES_Prime_complete in H3.
apply DCPS_complete2 in H3.
apply DCPS2_complete in H3.
apply DCPS3_complete in H3.
apply DCPS3N_complete in H3.
destruct H3 as [? H3].
apply DCPS4_complete in H3.
apply DCPS5_complete in H3.
apply ASTG_complete in H3.
apply STG_run_complete in H3...
split...
unfold subst...
rewrite apply_with_offset_0_id...
  (* *)
symmetry; apply empty_subst.
apply similar_empty.
apply empty_ok.
apply oa_empty_nil_nil.
  (* *)
auto.
discriminate.
(* right *)
assert (H2 : ($emptyA $ e ↓ Delta $ Constr C xs))...
apply values in H1.
destruct H1 as [[x0 [xs0]] | [C0 [xs0]]].
discriminate.
  (* *)
inversion H1; subst...
apply AAS_complete2 in H2.
apply EES_complete with (a := e) (beta := nil) (XiP := emptyB) in H2...
  (* *)
destruct H2 as [DeltaP [sigma [w [? [? [? []]]]]]].
exists DeltaP.
subst_inversion H5.
exists vs.
exists sigma.
split.
apply EES_Prime_complete in H3.
apply DCPS_complete2 in H3.
apply DCPS2_complete in H3.
apply DCPS3_complete in H3.
apply DCPS3N_complete in H3.
destruct H3 as [? H3].
apply DCPS4_complete in H3.
apply DCPS5_complete in H3.
apply ASTG_complete in H3.
apply STG_run_complete in H3...
split...
  (* *)
symmetry; apply empty_subst.
apply similar_empty.
apply empty_ok.
apply oa_empty_nil_nil.
Qed.

Proposition soundness :
forall (e f : expr) (DeltaP : heapB) (sigma : env) (Cs : list atom),
    closed_expr 0 e ->
    no_atoms e ->
    ($ Eval $ emptyB $ e $ nil $ nil $ nil -*-> DeltaP $ f $ sigma $ map Atom Cs) ->
exists Delta,
    similar Delta DeltaP /\
    ($ emptyA $ e ↓ Delta $ (f ~ [sigma] >< Cs)).
Proof with isa.
intros.
apply STG_run_sound in H1.
apply ASTG_sound in H1.
apply DCPS5_sound in H1.
apply DCPS4_sound in H1.
apply DCPS3_sound in H1.
apply DCPS2_sound in H1.
apply DCPSN_complete in H1; destruct H1 as [x].
apply DCPS_sound in H1.
apply EES_Prime_sound in H1.
apply EES_sound with (Gamma := emptyA) in H1...
rewrite empty_subst in H1.
destruct H1 as [Delta [? [? [?]]]]; exists Delta.
split...
apply AAS_sound2 in H1...
apply oa_empty_nil_nil.
apply empty_ok.
apply similar_empty.
Qed.

