Require Import List.
Require Import Arith.

(** * Compiling CCP to D *)

Require Import Common.
Require Import D.

Definition compile (e : CCP.expr) : D.expr := e.

Hint Constructors D.Sem CCP.Sem.

Lemma completeness_lemma :
forall Config Val0
  (CCPS : CCP.Sem Config Val0)
  Val1 K
  (DS : D.Sem (A Val0, K) Val1),
  D.Sem (E Config, K) Val1.
Proof with intros; eauto.
intros ? ? ?.
induction CCPS...
eapply D.App_Eval; try rewrite <- ARGSNIL...
Qed.

Lemma completeness :
forall Config Value
  (CCPS : CCP.Sem Config Value),
  D.Sem (E Config, nil) Value.
Proof with eauto.
intros; eapply completeness_lemma...
Qed.
