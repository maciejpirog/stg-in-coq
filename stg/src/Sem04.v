(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This is an additional semantics, which was not described in the paper.
Its sole puropse is to make some Coq proofs easier. *)

Require Export Sem03.

(** * Explicit Environment Semantics Prime *)

Reserved Notation "($ a $ b $ g $ e ↓↓↓↓ c $ d $ h $ f )"
  (at level 70, no associativity).

Inductive EES_Prime : heapB -> expr -> env -> vars -> heapB -> expr -> env ->
  vars -> Prop :=

| P_Con : forall Gamma C pi sigma,
  ($ Gamma $ Constr C pi $ sigma $ nil ↓↓↓↓ Gamma $ Constr C pi $ sigma $ nil)

| P_Accum : forall Gamma Delta x xm sigma_xm qn w rs sigma rho,
  xm <> nil ->
  env_map sigma xm = Some sigma_xm ->
  ($ Gamma $ App x nil $ sigma $ sigma_xm ++ qn ↓↓↓↓ Delta $ w $ rho $ rs) ->
  ($ Gamma $ App x xm  $ sigma $ qn             ↓↓↓↓ Delta $ w $ rho $ rs)

| P_App1 : forall Gamma p x pn m e sigma tau,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m > length pn ->
  ($ Gamma $ App x nil $ sigma $ pn ↓↓↓↓ Gamma $ App x nil $ sigma $ pn)

| P_App2_5 : forall Gamma Delta m e x tau p pn w rs sigma rho,
  env_find sigma x = Some (Atom p) ->
  Gamma p = Some (Lf_n m e, tau) ->
  m <= length pn -> 
  ($ Gamma $ e         $ zip_var_list m (firstn m pn) ++ shift m tau $ skipn m pn ↓↓↓↓ Delta $ w $ rho $ rs) ->
  ($ Gamma $ App x nil $ sigma                                       $ pn         ↓↓↓↓ Delta $ w $ rho $ rs)

| P_App4 : forall Gamma Delta sigma tau rho e p x C xs Theta w nu rs,
  env_find sigma x = Some (Atom p) -> 
  Gamma p = Some (Lf_u e, tau) ->
  ($ Gamma $ e         $ tau   $ nil ↓↓↓↓ Delta $ Constr C xs $ rho $ nil) ->
  ($ setB Delta p (Lf_n 0 (Constr C xs), trim rho xs) $ Constr C xs $ rho $ nil ↓↓↓↓ Theta $ w $ nu $ rs) ->
  ($ Gamma $ App x nil $ sigma $ nil ↓↓↓↓ Theta $ w $ nu $ rs)

| P_App5 : forall Gamma Delta Theta x p pn y q qk e f n w rs sigma rho nu
  mu tau,
  env_find sigma x = Some (Atom p) ->
  env_find rho y = Some (Atom q) ->
  Gamma p = Some (Lf_u e, tau) ->
  Delta q = Some (Lf_n n f, mu) ->
  length qk < n ->
  ($ Gamma $ e         $ tau   $ nil      ↓↓↓↓ Delta $ App y nil      $ rho $ qk) ->
  ($ setB Delta p (Lf_n (n - length qk) f, trim (zip_var_list (length qk) qk ++ shift (length qk) mu) (fv (Lf_n (n - length qk) f))) $
             App y nil $ rho   $ qk ++ pn ↓↓↓↓ Theta $ w              $ nu  $ rs) ->
  ($ Gamma $ App x nil $ sigma $ pn       ↓↓↓↓ Theta $ w              $ nu  $ rs)

| P_Let : forall Gamma Delta sigma rho lfs e w (ats : list nat) rs ss,
  length ats = length lfs ->
  (forall a : nat, In a ats -> Gamma a = None) -> 
  ($ allocB Gamma ats
      (map (fun lf => (lf, trim (zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma) (fv lf))) lfs)
    $ e $ zip_var_list (length lfs) (map Atom ats) ++ shift (length lfs) sigma $ rs
    ↓↓↓↓ Delta $ w $ rho $ ss) ->
  ($ Gamma $ Letrec lfs e $ sigma $ rs ↓↓↓↓ Delta $ w $ rho $ ss)

| P_Case_of : forall Gamma Delta Theta b e e0 als ys w c c0 rho_ys rs qs
  sigma rho nu,
  length ys = b ->
  env_map rho ys = Some rho_ys ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Gamma $ e          $ sigma                                  $ nil ↓↓↓↓ Delta $ Constr c ys $ rho $ nil) ->
  ($ Delta $ e0         $ zip_var_list b rho_ys ++ shift b sigma $ qs  ↓↓↓↓ Theta $ w           $ nu $ rs) ->
  ($ Gamma $ Case e als $ sigma                                  $ qs  ↓↓↓↓ Theta $ w           $ nu $ rs)

where "($ a $ b $ g $ e ↓↓↓↓ c $ d $ h $ f )" :=
  (EES_Prime a b g e c d h f).

Hint Constructors EES_Prime.

(** * Completeness and soundness *)

Proposition EES_Prime_complete :
forall Gamma Delta e f theta rho ps qs,
  ($ Gamma $ e $ theta $ ps ↓↓↓ Delta $ f $ rho $ qs) ->
  ($ Gamma $ e $ theta $ ps ↓↓↓↓ Delta $ f $ rho $ qs).
Proof with eauto.
intros...
induction H...
Qed.

Proposition EES_Prime_sound :
forall Gamma Delta e f theta rho ps qs,
  ($ Gamma $ e $ theta $ ps ↓↓↓↓ Delta $ f $ rho $ qs) ->
  ($ Gamma $ e $ theta $ ps ↓↓↓ Delta $ f $ rho $ qs).
Proof with eauto.
intros.
induction H...
inversion H2; subst...
Qed.
