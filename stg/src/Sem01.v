(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains the definition of the natural semantics
for the STG language. *)

Require Export Heaps.

(** * The STG language natural semantics *)

Reserved Notation "($ a $ b ↓ c $ d )" (at level 70, no associativity).

Inductive STG : heapA -> expr -> heapA -> expr -> Prop :=

| Con : forall Gamma C vs,
  ($Gamma $ Constr C vs ↓ Gamma $ Constr C vs)

| App1 : forall Gamma p pn m e,
  Gamma p = Some (Lf_n m e) ->
  m > length pn ->
  ($ Gamma $ App p pn ↓ Gamma $ App p pn)

| App2 : forall Gamma Delta p e pn m w,
  Gamma p = Some (Lf_n m e) ->
  m = length pn ->
  ($ Gamma $ e~[zip_var_list m pn] ↓ Delta $ w) ->
  ($ Gamma $ App p pn ↓ Delta $ w)

| App3 : forall Gamma Delta Theta q qk p e pm m w,
  Gamma p = Some (Lf_n m e) ->
  m < length pm ->
  ($ Gamma $ e~[zip_var_list m (firstn m pm)] ↓ Delta $ App q qk) ->
  ($ Delta $ App q (qk ++ skipn m pm) ↓ Theta $ w) ->
  ($ Gamma $ App p pm ↓ Theta $ w)

| App4 : forall Gamma Delta e p C qs,
  Gamma p = Some (Lf_u e) ->
  ($ Gamma $ e ↓ Delta $ Constr C qs) ->
  ($ Gamma $ App p nil ↓ setA Delta p (Lf_n 0 (Constr C qs)) $ Constr C qs)

| App5 : forall Gamma Delta Theta p pn q qk e f n w,
  Gamma p = Some (Lf_u e) ->
  Delta q = Some (Lf_n n f) ->
  length qk < n ->
  ($ Gamma $ e ↓ Delta $ App q qk) ->
  ($ setA Delta p (Lf_n (n - length qk) (f~[zip_var_list n qk])) $
    App q (qk ++ pn) ↓ Theta $ w) ->
  ($ Gamma $ App p pn ↓ Theta $ w)

| Let : forall Gamma Delta lfs e w ats,
  length ats = length lfs ->
  are_atoms ats ->
  (forall a : var, In a ats -> Gamma a = None) -> 
  ($ allocA Gamma ats
      (map (subst_lf (zip_var_list (length lfs) ats)) lfs)
    $ e~[zip_var_list (length lfs) ats]
    ↓ Delta $ w) ->
  ($ Gamma $ Letrec lfs e ↓ Delta $ w) 

| Case_of : forall Gamma Delta Theta b e e0 als w c c0 ps,
  length ps = b ->
  select_case als c = Some (Alt c0 b e0) ->
  ($ Gamma $ e ↓ Delta $ Constr c ps) ->
  ($ Delta $ e0~[zip_var_list b ps] ↓ Theta $ w) ->
  ($ Gamma $ Case e als ↓ Theta $ w)

where "($ a $ b ↓ c $ d )" := (STG a b c d).

Hint Resolve Con App1 App2 App3 App4 App5 Let Case_of.
