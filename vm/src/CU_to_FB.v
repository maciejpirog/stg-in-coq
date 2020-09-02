Require Import List.
Require Import Arith.

Require Import Common.
Require Import FB.

(** * Compiling CU to FB *)

Definition compile (e : CU.expr) : FB.expr := e.

Create HintDb cu_fb.

Hint Constructors FB.Sem : cu_fb.

Lemma invariant :
forall Config Value tau
  (EVAL : CU.Sem Config (Value, tau)),
  match Config with
  | CU.Config Gamma e sigma args clo => forall (args0 : argstack),
      FB.Sem (FB.Config Gamma e sigma (args++args0, length args0) clo)
             (Value, tau, (args0, length args0))
  | CU.Enter Gamma p args sigma => forall (args0 : argstack),
      FB.Sem (FB.Enter Gamma p (args++args0, length args0) sigma)
             (Value, tau, (args0, length args0))
  end.
Proof with isa; auto with cu_fb.
intros.
induction EVAL...
(* Case Accum *)
apply FB.Accum with (p := p) (new_args := new_args)...
rewrite <- app_ass...
(* Case App1 *)
apply FB.App1 with (clovars := clovars) (bind := bind) (e := e)
  (some_clo := some_clo)...
rewrite app_length; rewrite plus_comm; rewrite minus_plus;
  apply firstn_app.
rewrite app_length; rewrite plus_comm; rewrite minus_plus;
  apply skipn_app.
rewrite app_length; rewrite plus_comm; rewrite minus_plus...
(* Case App2 *)
apply FB.App2 with (e := e) (bind := bind) (clo := clo)
  (clovars := clovars)...
rewrite app_length; rewrite plus_comm; rewrite minus_plus...
cutrewrite (firstn bind (args ++ args0) = firstn bind args).
cutrewrite (skipn bind (args ++ args0) = skipn bind args ++ args0)...
apply skipn_app2...
apply firstn_app2...
(* Case App3 *)
apply FB.App3 with (clovars := clovars) (e := e) (clo := clo)...
(* Case App4 *)
eapply FB.App4; eauto.
rewrite <- app_ass...
(* Case Let *)
apply FB.Let with (closures := closures) (addrs := addrs)...
(* Case Case_of *)
eapply FB.Case_of...
apply SELECT.
Qed.

Lemma completeness :
forall Config Value tau
  (EVAL : CU.Sem Config (Value, tau)),
  match Config with
  | CU.Config Gamma e sigma args clo =>
      FB.Sem (FB.Config Gamma e sigma (args, 0) clo)
             (Value, tau, (nil, 0))
  | CU.Enter Gamma p args sigma =>
      FB.Sem (FB.Enter Gamma p (args, 0) sigma)
             (Value, tau, (nil, 0))
  end.
Proof with isa.
intros.
assert (I := invariant Config Value tau EVAL).
destruct Config;
remember (I nil) as I2; clear HeqI2;
autorewrite with list in I2...
Qed.

