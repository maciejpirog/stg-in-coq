(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains the definition of the D-CPS
semantics and proof of its equivalence with the previous semantics. *)

Require Export Sem04.
Require Import Arith.Max.

(** * Defunctionalized Continuation Passing Style Semantics *)

Inductive action : Set := E | A.

Inductive stack_elem : Set :=
| S_alt : alts -> env -> vars -> stack_elem
| S_upd : var -> vars -> stack_elem.

Definition stack := list stack_elem.

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive DCPS : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| D_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\ Gamma $ w $ sigma $ ps)

| D_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\ Delta $ w $ rho $ qs)

| D_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\ Delta $ w $ rho $ rs)

| D_App1 : forall Gamma tau p x pn m e sigma Delta rho w rs Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ A $ Gamma $ App x nil $ sigma $ pn $ Ss ^\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ Ss ^\ Delta $ w $ rho $ rs)

| D_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\ Delta $ w $ rho $ rs)

| DA_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\ Theta $ w $ nu $ qs)

| DE_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\ Theta $ w $ nu $ qs) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\ Theta $ w $ nu $ qs)

| DA_App5 : forall Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\ Theta $ w $ nu $ qs)

| D_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\ Delta $ w $ rho $ qs)

| DE_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\ Theta $ w $ nu $ rs) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\ Theta $ w $ nu $ rs)

| DA_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\ Theta $ w $ nu $ rs) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^\ c $ d $ h $ f )" :=
  (DCPS x a b g e s c d h f).

Hint Constructors DCPS.

(** * Completeness *)

Proposition DCPS_complete :
forall Xi e beta Ps Psi b gamma Qs,
  ($ Xi $ e $ beta $ Ps ↓↓↓↓ Psi $ b $ gamma $ Qs) ->
forall Omega c xi Rs Ts,
  ($ E $ Psi $ b $ gamma $ Qs $ Ts ^\ Omega $ c $ xi $ Rs) ->
  ($ E $ Xi  $ e $ beta  $ Ps $ Ts ^\ Omega $ c $ xi $ Rs).
Proof with intuition; eauto.
intros ? ? ? ? ? ? ? ? P.
induction P; intros...
(* [3] Case App4 *)
eapply DE_App4_5...
(* [2] Case App5 *)
eapply DE_App4_5...
(* [1] Case Case *)
eapply DE_Case_of...
Qed.

Lemma EES_values :
forall Xi e beta Ps Psi b gamma Qs,
  ($ Xi $ e $ beta $ Ps ↓↓↓↓ Psi $ b $ gamma $ Qs) ->
  (exists C, exists xs, b = Constr C xs /\ Qs = nil)
  \/
  (exists x, exists p, exists m, exists f, exists tau,
    b = App x nil /\
    env_find gamma x = Some (Atom p) /\
    Psi p = Some (Lf_n m f, tau) /\
    m > length Qs).
Proof with isa; intuition.
intros.
induction H.
left; exists C; exists pi...
destruct IHEES_Prime...
right; exists x; exists p; exists m; exists e; exists tau...
destruct IHEES_Prime...
destruct IHEES_Prime2...
destruct IHEES_Prime2...
destruct IHEES_Prime...
destruct IHEES_Prime2...
Qed.

Proposition DCPS_complete2 :
forall Xi e beta Ps Psi b gamma Qs,
  ($     Xi $ e $ beta $ Ps     ↓↓↓↓ Psi $ b $ gamma $ Qs) ->
  ($ E $ Xi $ e $ beta $ Ps $ nil ^\ Psi $ b $ gamma $ Qs).
Proof with isa.
intros.
dupl H.
apply EES_values in H.
destruct H.
(* left *)
destruct H as [C [xs [W1 W2]]]; subst.
apply DCPS_complete with (Omega := Psi) (c := Constr C xs) (xi := gamma)
  (Rs := nil) (Ts := nil) in H0...
(* right *)
destruct H as [x [p [m [f [tau [W1 [W2 [W3 W4]]]]]]]]; subst.
apply DCPS_complete with (Omega := Psi) (c := App x nil) (xi := gamma)
  (Rs := Qs) (Ts := nil) in H0...
eapply D_App1; eauto.
Qed.


(** * Soundness *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\ c $ d $ h $ f ^^ n )"
  (at level 70, no associativity).

Inductive DCPSN : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> nat -> Prop :=

| D_HaltN : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\ Gamma $ w $ sigma $ ps ^^ 0)

| D_ConN : forall Gamma Delta C pi w sigma rho qs Ss n,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\ Delta $ w $ rho $ qs ^^ n) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\ Delta $ w $ rho $ qs ^^ S n)

| D_AccumN : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss n,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\ Delta $ w $ rho $ rs ^^ n) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\ Delta $ w $ rho $ rs ^^ S n)

| D_App1N : forall Gamma tau p x pn m e sigma Delta rho w rs Ss n,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ A $ Gamma $ App x nil $ sigma $ pn $ Ss ^\ Delta $ w $ rho $ rs ^^ n) ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ Ss ^\ Delta $ w $ rho $ rs ^^ S n)

| D_App2_5N : forall Gamma Delta m e x tau p pn w rs sigma rho Ss n,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\ Delta $ w $ rho $ rs ^^ n) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\ Delta $ w $ rho $ rs ^^ S n)

| DA_App4N : forall Delta rho C xs p Theta w nu qs Ss n,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\ Theta $ w $ nu $ qs ^^ n) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\ Theta $ w $ nu $ qs ^^ S n)

| DE_App4_5N : forall Gamma Theta x p w e tau sigma nu rs qs Ss n,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\ Theta $ w $ nu $ qs ^^ n) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\ Theta $ w $ nu $ qs ^^ S n)

| DA_App5N : forall Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss m,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\ Theta $ w $ nu $ qs ^^ m) ->
  ($ A $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\ Theta $ w $ nu $ qs ^^ S m)

| D_LetN : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss n,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\ Delta $ w $ rho $ qs ^^ n) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\ Delta $ w $ rho $ qs ^^ S n)

| DE_Case_ofN : forall Gamma Theta e als w rs qs sigma nu Ss n,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\ Theta $ w $ nu $ rs ^^ n) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\ Theta $ w $ nu $ rs ^^ S n)

| DA_Case_ofN : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss n,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\ Theta $ w $ nu $ rs ^^ n) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\ Theta $ w $ nu $ rs ^^ S n) 

where "($ x $ a $ b $ g $ e $ s ^\ c $ d $ h $ f ^^ n )" :=
  (DCPSN x a b g e s c d h f n).

Hint Constructors DCPSN.

Lemma DCPSN_complete :
forall X Gamma e sigma rs Ss Delta f rho qs,
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ^\ Delta $ f $ rho $ qs) ->
  exists N,
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ^\ Delta $ f $ rho $ qs ^^ N).
Proof.
intros; induction H; eauto; destruct IHDCPS; eauto.
Qed.

Lemma DCPSN_sound :
forall X Gamma e sigma rs Ss Delta f rho qs N,
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ^\ Delta $ f $ rho $ qs ^^ N) ->
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ^\ Delta $ f $ rho $ qs).
Proof.
intros; induction H; eauto.
Qed.

Ltac destruct_exists H :=
  let X := fresh "x" in destruct H as [X H]; exists X.

Ltac destruct_exists_ind H :=
  (do 4 destruct_exists H);
  let X := fresh "x" in destruct H as [X H]; exists (S X);
  destruct_exists H;
  split; intuition; eauto.

Lemma DCPS_split :
forall N X Gamma e sigma rs Ss Ts Delta f rho qs,
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ++ Ts
      ^\ Delta $ f $ rho $ qs ^^ N) ->
  exists Psi, exists c, exists gamma, exists Qs, exists N0, exists N1,
    ($ X $ Gamma $ e $ sigma $ rs $ Ss ^\ Psi $ c $ gamma $ Qs ^^ N0) /\
    ($ A $ Psi $ c $ gamma $ Qs $ Ts ^\ Delta $ f $ rho $ qs ^^ N1) /\
    N0 <= N /\ N1 <= N.
Proof with intuition; eauto.
intro N.
induction N using lt_wf_ind; isa.
destruct N; inversion H0; subst.
(* [11] Case *)
apply nil_app in H7.
destruct H7.
subst.
exists Delta.
exists f.
exists rho.
exists qs.
exists 0.
exists 0...
(* [10] Case *)
apply H in H12...
destruct_exists_ind H12.
(* [9] Case *)
apply H in H14...
destruct_exists_ind H14.
(* [8] Case *)
apply H in H15...
destruct_exists_ind H15.
(* [7] Case *)
apply H in H15...
destruct_exists_ind H15.
(* [6] Case *)
apply cons_cons_app in H1.
destruct H1.
  (* subcase *)
destruct H1.
subst.
apply H with (Ss := nil) in H12...
exists Gamma.
exists (Constr C xs).
exists sigma.
exists nil.
exists 0.
exists (S N).
split...
  (* subcase *)
destruct H1 as [x []]; subst.
apply H in H12...
destruct_exists_ind H12.
(* [5] Case *)
rewrite app_comm_cons in *.
apply H in H14...
destruct_exists_ind H14.
(* [4] Case *)
apply cons_cons_app in H1.
destruct H1.
  (* subcase *)
destruct H1.
subst.
apply H with (Ss := nil) in H16...
exists Gamma.
exists (App y nil).
exists sigma.
exists rs.
exists 0.
exists (S N).
split...
  (* subcase *)
do 2 destruct H1.
subst.
apply H in H16...
destruct_exists_ind H16.
(* [3] Case *)
apply H in H14...
destruct_exists_ind H14.
(* [2] Case *)
rewrite app_comm_cons in *.
apply H in H12...
destruct_exists_ind H12.
(* [1] Case *)
apply cons_cons_app in H1.
destruct H1.
  (* subcase *)
destruct H1.
subst.
apply H with (Ss := nil) in H15...
exists Gamma.
exists (Constr c ys).
exists sigma.
exists nil.
exists 0.
exists (S N).
split...
  (* subcase *)
do 2 destruct H1.
subst.
apply H in H15...
destruct_exists_ind H15.
Qed.

Lemma DCPS_sound :
forall N Xi e beta Ps Psi b gamma Qs,
  ($ E $ Xi $ e $ beta $ Ps $ nil ^\ Psi $ b $ gamma $ Qs ^^ N) ->
  ($ Xi $ e $ beta $ Ps ↓↓↓↓ Psi $ b $ gamma $ Qs).
Proof with subst; intuition; isa; eauto.
induction N using lt_wf_ind; isa.
destruct N;
  inversion H0...
(* [4] Case *)
inversion H2...
(* [3] Case *)
inversion H5...
(* [2] Case *)
apply DCPS_split with (Ss := nil) in H4.
do 6 destruct H4 as [ ? H4 ]...
inversion H4; subst; apply H in H1...
(* [1] Case *)
apply DCPS_split with (Ss := nil) in H2.
destruct H2.
do 6 destruct H1...
inversion H3...
apply H in H1...
Qed.
