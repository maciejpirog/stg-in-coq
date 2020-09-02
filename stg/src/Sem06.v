(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains proofs of equivalence of semantics created
by merging and splitting some rules of the DCPS semantics.
In the paper it is done a little different, since it was easier
(but less readable) to do it in Coq before switching to an
abstract machine. *)

Require Export Sem05.

(** * Defunctionalized Continuation Passing Style Semantics 2 *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\\ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive DCPS2 : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| D2_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\\ Gamma $ w $ sigma $ ps)

| D2_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\ Delta $ w $ rho $ qs)

| D2_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\\ Delta $ w $ rho $ rs)

| D2_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ nil ^\\ Gamma $ App x nil $ sigma $ pn)

| D2_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\\ Delta $ w $ rho $ rs)

| D2A_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\\ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\\ Theta $ w $ nu $ qs)

| D2E_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\\ Theta $ w $ nu $ qs) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\\ Theta $ w $ nu $ qs)

| D2A_App5 : forall EA Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E  $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\\ Theta $ w $ nu $ qs) ->
  ($ EA $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\\ Theta $ w $ nu $ qs)

| D2_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\\ Delta $ w $ rho $ qs)

| D2E_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\\ Theta $ w $ nu $ rs) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\\ Theta $ w $ nu $ rs)

| D2A_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\\ Theta $ w $ nu $ rs) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\\ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^\\ c $ d $ h $ f )" :=
  (DCPS2 x a b g e s c d h f).

Hint Constructors DCPS2.

Lemma DCPS2_complete :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\  Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\ Delta $ f $ rho $ qn).
Proof with isa; eauto.
intros.
induction H...
destruct Ss.
  (* nil *)
inversion H2; subst...
  (* cons *)
inversion IHDCPS; subst...
Qed.

Lemma DCPS2_sound :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\ Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\  Delta $ f $ rho $ qn).
Proof with isa; eauto.
intros.
induction H...
destruct EA...
Qed.


(** * Defunctionalized Continuation Passing Style Semantics 3 *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\\\ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive DCPS3 : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| D3_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\\\ Gamma $ w $ sigma $ ps)

| D3_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\\ Delta $ w $ rho $ qs)

| D3_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\\\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\\\ Delta $ w $ rho $ rs)

| D3_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ nil ^\\\ Gamma $ App x nil $ sigma $ pn)

| D3_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\\\ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\\\ Delta $ w $ rho $ rs)

| D3A_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\\\ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\\\ Theta $ w $ nu $ qs)

| D3E_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\\\ Theta $ w $ nu $ qs) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\\\ Theta $ w $ nu $ qs)

| D3A_App5 : forall EA Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\\\ Theta $ w $ nu $ qs) ->
  ($ EA $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\\\ Theta $ w $ nu $ qs)

| D3_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\\\ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\\\ Delta $ w $ rho $ qs)

| D3E_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\\\ Theta $ w $ nu $ rs) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\\\ Theta $ w $ nu $ rs)

| D3A_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\\\ Theta $ w $ nu $ rs) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\\\ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^\\\ c $ d $ h $ f )" :=
  (DCPS3 x a b g e s c d h f).

Hint Constructors DCPS3.

Lemma DCPS3_complete :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\  Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\\ Delta $ f $ rho $ qn).
Proof.
intros.
induction H; eauto.
Qed.

Lemma DCPS3_sound :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\\ Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\  Delta $ f $ rho $ qn).
Proof.
intros.
induction H; eauto.
Qed.


(** * Defunctionalized Continuation Passing Style Semantics 3 N *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^^\\\ c $ d $ h $ f ^^ n )"
  (at level 70, no associativity).

Inductive DCPS3N : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> nat -> Prop :=

| D3N_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^^\\\ Gamma $ w $ sigma $ ps ^^ 0)

| D3N_Con : forall Gamma Delta C pi w sigma rho qs Ss N,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^^\\\ Delta $ w $ rho $ qs ^^ N) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^^\\\ Delta $ w $ rho $ qs ^^ S N)

| D3N_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss N,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^^\\\ Delta $ w $ rho $ rs ^^ N) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^^\\\ Delta $ w $ rho $ rs ^^ S N)

| D3N_App1 : forall Gamma tau p x pn m e sigma,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ nil ^^\\\ Gamma $ App x nil $ sigma $ pn ^^ 0)

| D3N_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss N,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^^\\\ Delta $ w $ rho $ rs ^^ N) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^^\\\ Delta $ w $ rho $ rs ^^ S N)

| D3NA_App4 : forall Delta rho C xs p Theta w nu qs Ss N,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^^\\\ Theta $ w $ nu $ qs ^^ N) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^^\\\ Theta $ w $ nu $ qs ^^ S N)

| D3NE_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss N,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^^\\\ Theta $ w $ nu $ qs ^^ N) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^^\\\ Theta $ w $ nu $ qs ^^ S N)

| D3NA_App5 : forall EA Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss N,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^^\\\ Theta $ w $ nu $ qs ^^ N) ->
  ($ EA $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^^\\\ Theta $ w $ nu $ qs ^^ S N)

| D3N_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss N,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^^\\\ Delta $ w $ rho $ qs ^^ N) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^^\\\ Delta $ w $ rho $ qs ^^ S N)

| D3NE_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss N,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^^\\\ Theta $ w $ nu $ rs ^^ N) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^^\\\ Theta $ w $ nu $ rs ^^ S N)

| D3NA_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss N,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^^\\\ Theta $ w $ nu $ rs ^^ N) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^^\\\ Theta $ w $ nu $ rs ^^ S N) 

where "($ x $ a $ b $ g $ e $ s ^^\\\ c $ d $ h $ f ^^ n )" :=
  (DCPS3N x a b g e s c d h f n).

Hint Constructors DCPS3N.

Lemma DCPS3N_complete :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\\  Delta $ f $ rho $ qn) ->
  exists N,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^^\\\ Delta $ f $ rho $ qn ^^ N).
Proof with eauto.
intros.
induction H; try eauto;
  destruct IHDCPS3 as [N]; exists (S N); try constructor...
Qed.

Lemma DCPS3N_sound :
forall EA N Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^^\\\ Delta $ f $ rho $ qn ^^ N) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\\  Delta $ f $ rho $ qn).
Proof with isa; eauto.
intros.
induction H...
Qed.


(** * Defunctionalized Continuation Passing Style Semantics 4 *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\\/ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive DCPS4 : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| D4_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\\/ Gamma $ w $ sigma $ ps)

| D4_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\/ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\\/ Delta $ w $ rho $ qs)

| D4_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\\/ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\\/ Delta $ w $ rho $ rs)

| D4_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ nil ^\\/ Gamma $ App x nil $ sigma $ pn)

| D4_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\\/ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\\/ Delta $ w $ rho $ rs)

| D4A_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ E $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\\/ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\\/ Theta $ w $ nu $ qs)

| D4E_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\\/ Theta $ w $ nu $ qs) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\\/ Theta $ w $ nu $ qs)

| D4A_App5 : forall Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\\/ Theta $ w $ nu $ qs) ->
  ($ E $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\\/ Theta $ w $ nu $ qs)

| D4_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\\/ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\\/ Delta $ w $ rho $ qs)

| D4E_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\\/ Theta $ w $ nu $ rs) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\\/ Theta $ w $ nu $ rs)

| D4A_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\\/ Theta $ w $ nu $ rs) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\\/ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^\\/ c $ d $ h $ f )" :=
  (DCPS4 x a b g e s c d h f).

Hint Constructors DCPS4.

Lemma DCPS4_complete :
forall N Gamma e sigma pn Ss Delta f rho qn,
  ($ E $ Gamma $ e $ sigma $ pn $ Ss ^^\\\ Delta $ f $ rho $ qn ^^ N) ->
  ($ E $ Gamma $ e $ sigma $ pn $ Ss ^\\/  Delta $ f $ rho $ qn).
Proof with eauto.
intro N.
induction N using lt_wf_ind; isa.
inversion H0; subst...
inversion H0; subst...
constructor.
inversion H7; subst...
Qed.

Lemma DCPS4_sound :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\/ Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\\  Delta $ f $ rho $ qn).
Proof.
intros.
induction H; eauto.
Qed.


(** * Defunctionalized Continuation Passing Style Semantics 5 *)

Reserved Notation "($ x $ a $ b $ g $ e $ s ^\/ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive DCPS5 : action -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| D5_Halt : forall Gamma w sigma ps,
  ($ A $ Gamma $ w $ sigma $ ps $ nil ^\/ Gamma $ w $ sigma $ ps)

| D5_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ A $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\/ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^\/ Delta $ w $ rho $ qs)

| D5_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ E $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^\/ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^\/ Delta $ w $ rho $ rs)

| D5_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ E $ Gamma $ App x nil $ sigma $ pn $ nil ^\/ Gamma $ App x nil $ sigma $ pn)

| D5_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ E $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^\/ Delta $ w $ rho $ rs) ->
  ($ E $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^\/ Delta $ w $ rho $ rs)

| D5A_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ A $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^\/ Theta $ w $ nu $ qs) ->
  ($ A $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^\/ Theta $ w $ nu $ qs)

| D5E_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ E $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^\/ Theta $ w $ nu $ qs) ->
  ($ E $ Gamma $ App x nil $ sigma $ rs $ Ss ^\/ Theta $ w $ nu $ qs)

| D5A_App5 : forall Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ E $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^\/ Theta $ w $ nu $ qs) ->
  ($ E $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^\/ Theta $ w $ nu $ qs)

| D5_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ E $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^\/ Delta $ w $ rho $ qs) ->
  ($ E $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^\/ Delta $ w $ rho $ qs)

| D5E_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ E $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^\/ Theta $ w $ nu $ rs) ->
  ($ E $ Gamma $ Case e als $ sigma $ qs $ Ss ^\/ Theta $ w $ nu $ rs)

| D5A_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ E $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^\/ Theta $ w $ nu $ rs) ->
  ($ A $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^\/ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^\/ c $ d $ h $ f )" :=
  (DCPS5 x a b g e s c d h f).

Hint Constructors DCPS5.

Lemma DCPS5_complete :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\/ Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\/  Delta $ f $ rho $ qn).
Proof with eauto.
intros.
induction H...
inversion IHDCPS4; subst...
Qed.

Lemma DCPS5_sound :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\/  Delta $ f $ rho $ qn) ->
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\\/ Delta $ f $ rho $ qn).
Proof.
intros.
induction H; eauto.
Qed.


(** * The STG Almost-Machine *)

Inductive instruction := Eval | Enter | ReturnCon.

Reserved Notation "($ x $ a $ b $ g $ e $ s ^^^ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive ASTG : instruction -> heapB -> expr -> env -> vars -> stack ->
  heapB -> expr -> env -> vars -> Prop :=

| ASTG_Halt : forall Gamma w sigma ps,
  ($ ReturnCon $ Gamma $ w $ sigma $ ps $ nil ^^^ Gamma $ w $ sigma $ ps)

| ASTG_Con : forall Gamma Delta C pi w sigma rho qs Ss,
  ($ ReturnCon $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^^^ Delta $ w $ rho $ qs) ->
  ($ Eval      $ Gamma $ Constr C pi $ sigma $ nil $ Ss ^^^ Delta $ w $ rho $ qs)

| ASTG_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho Ss,
  (* We abandon xm <> nil *)
  env_map sigma xm = Some sigma_xm ->
  ($ Enter $ Gamma $ App x nil $ sigma $ sigma_xm ++ qn $ Ss ^^^ Delta $ w $ rho $ rs) ->
  ($ Eval  $ Gamma $ App x xm  $ sigma $ qn             $ Ss ^^^ Delta $ w $ rho $ rs)

| ASTG_App1 : forall Gamma tau p x pn m e sigma ,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ Enter $ Gamma $ App x nil $ sigma $ pn $ nil ^^^ Gamma $ App x nil $ sigma $ pn)

| ASTG_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho Ss,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ Eval  $ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn $ Ss ^^^ Delta $ w $ rho $ rs) ->
  ($ Enter $ Gamma $ App x nil $ sigma                                          $ pn         $ Ss ^^^ Delta $ w $ rho $ rs)

| ASTGA_App4 : forall Delta rho C xs p Theta w nu qs Ss,
  ($ ReturnCon $ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil $ Ss ^^^ Theta $ w $ nu $ qs) ->
  ($ ReturnCon $ Delta $ Constr C xs $ rho $ nil $ S_upd (Atom p) nil :: Ss ^^^ Theta $ w $ nu $ qs)

| ASTGE_App4_5 : forall Gamma Theta x p w e tau sigma nu rs qs Ss,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ Eval  $ Gamma $ e         $ tau   $ nil $ S_upd (Atom p) rs :: Ss ^^^ Theta $ w $ nu $ qs) ->
  ($ Enter $ Gamma $ App x nil $ sigma $ rs $ Ss ^^^ Theta $ w $ nu $ qs)

| ASTGA_App5 : forall Delta Theta x p pn y q qk f n w sigma rho nu mu qs Ss,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ Enter $ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho $ qk ++ pn $ Ss    ^^^ Theta $ w $ nu $ qs) ->
  ($ Enter $ Delta $ App y nil $ rho $ qk $ S_upd (Atom p) pn :: Ss ^^^ Theta $ w $ nu $ qs)

| ASTG_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs qs Ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ Eval $ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs $ Ss
    ^^^ Delta $ w $ rho $ qs) ->
  ($ Eval $ Gamma $ Letrec lfs e $ sigma $ rs $ Ss ^^^ Delta $ w $ rho $ qs)

| ASTGE_Case_of : forall Gamma Theta e als w rs qs sigma nu Ss,
  ($ Eval $ Gamma $ e          $ sigma $ nil $ S_alt als sigma qs :: Ss ^^^ Theta $ w $ nu $ rs) ->
  ($ Eval $ Gamma $ Case e als $ sigma $ qs $ Ss ^^^ Theta $ w $ nu $ rs)

| ASTGA_Case_of : forall Delta Theta b e0 als ys w c c0 rho_ys rs qs
  sigma rho nu Ss,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Eval $ Delta $ e0          $ zip_var_list b rho_ys ++ shift b sigma $ qs $ Ss ^^^ Theta $ w $ nu $ rs) ->
  ($ ReturnCon $ Delta $ Constr c ys $ rho $ nil $ S_alt als sigma qs :: Ss                ^^^ Theta $ w $ nu $ rs) 

where "($ x $ a $ b $ g $ e $ s ^^^ c $ d $ h $ f )" :=
  (ASTG x a b g e s c d h f).

Hint Constructors ASTG.

Definition action_to_instruction (a : action) (e : expr) : instruction :=
match a with
| A => ReturnCon
| E => match e with
  | App _ nil => Enter
  | _         => Eval
  end
end.

Lemma ASTG_complete_aux :
forall EA Gamma e sigma pn Ss Delta f rho qn,
  ($ EA $ Gamma $ e $ sigma $ pn $ Ss ^\/  Delta $ f $ rho $ qn) ->
  ($ action_to_instruction EA e $ Gamma $ e $ sigma $ pn $ Ss ^^^ Delta $ f $ rho $ qn).
Proof with isa.
intros.
induction H...
(* Case *)
destruct xm...
case H...
econstructor; eauto.
(* Case *)
econstructor; eauto.
(* Case *)
destruct e; econstructor; eauto.
destruct v0; eauto.
apply ASTG_Accum with (sigma_xm := nil); eauto.
(* Case *)
destruct e; econstructor 7; eauto.
destruct v0; eauto.
apply ASTG_Accum with (sigma_xm := nil); eauto.
(* Case *)
econstructor 8; eauto.
(* Case *)
destruct e; econstructor; eauto.
destruct v0; eauto.
apply ASTG_Accum with (sigma_xm := nil); eauto.
(* Case *)
destruct e; econstructor; eauto.
destruct v0; eauto.
apply ASTG_Accum with (sigma_xm := nil); eauto.
(* Case *)
destruct e0; econstructor; eauto.
destruct v0; eauto.
apply ASTG_Accum with (sigma_xm := nil); eauto.
Qed.

Lemma ASTG_complete :
forall Gamma e sigma pn Ss Delta f rho qn,
  ($ E    $ Gamma $ e $ sigma $ pn $ Ss ^\/ Delta $ f $ rho $ qn) ->
  ($ Eval $ Gamma $ e $ sigma $ pn $ Ss ^^^ Delta $ f $ rho $ qn).
Proof with isa.
intros.
destruct e.
(* Case *)
destruct v0.
  (* Subcase *)
apply ASTG_Accum with (sigma_xm := nil)...
fold (action_to_instruction E (App v nil)).
apply ASTG_complete_aux...
  (* Subcase *)
fold (action_to_instruction E (App v (v0 :: v1))).
apply ASTG_complete_aux...
(* Case *)
fold (action_to_instruction E (Constr c v)).
apply ASTG_complete_aux...
(* Case *)
fold (action_to_instruction E (Letrec l e)).
apply ASTG_complete_aux...
(* Case *)
fold (action_to_instruction E (Case e l)).
apply ASTG_complete_aux...
Qed.

Definition instruction_to_action (i : instruction) : action :=
match i with
| ReturnCon => A
| _ => E
end.

Lemma ASTG_sound_aux :
forall REE Gamma e sigma pn Ss Delta f rho qn,
  ($ REE $ Gamma $ e $ sigma $ pn $ Ss ^^^ Delta $ f $ rho $ qn) ->
  ($ instruction_to_action REE $ Gamma $ e $ sigma $ pn $ Ss ^\/ Delta $ f $ rho $ qn).
Proof with isa.
intros.
induction H...
(* Case *)
destruct xm.
  (* Subcase *)
simpl in H.
inversion H; subst...
  (* Subcase *)
eapply D5_Accum; eauto.
discriminate.
(* Case *)
eapply D5_App1; eauto.
(* Case *)
eapply D5_App2_5; eauto.
(* Case *)
eapply D5E_App4_5; eauto.
(* Case *)
eapply D5A_App5; eauto.
(* Case *)
econstructor; eauto.
(* Case *)
econstructor; eauto.
Qed.

Lemma ASTG_sound :
forall Gamma e sigma pn Ss Delta f rho qn,
  ($ Eval $ Gamma $ e $ sigma $ pn $ Ss ^^^ Delta $ f $ rho $ qn) ->
  ($ E    $ Gamma $ e $ sigma $ pn $ Ss ^\/ Delta $ f $ rho $ qn).
Proof with isa.
intros.
fold (instruction_to_action Eval).
apply ASTG_sound_aux...
Qed.

