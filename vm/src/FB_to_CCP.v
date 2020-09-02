Require Import List.
Require Import Arith.

Require Import CCP.
Require Import FB.
Require Import Common.

(** * Compiling FB to CCP *)

Definition compile (e : FB.expr) : CCP.expr := e.

Hint Constructors CCP.Sem : fb_ccp.

Lemma look_up_equiv :
forall Gamma sigma pe clo pclo v addr
  (PCLO   : Gamma pclo = Some (pe, clo))
  (LOOKUP : look_up sigma clo v = addr),
  CCP.look_up sigma Gamma pclo v = addr.
Proof with isa.
intros.
destruct v as [n | n]...
rewrite PCLO...
Qed.

Lemma map_env_equiv :
forall Gamma sigma pe clo pclo vs addrs
  (PCLO   : Gamma pclo = Some (pe, clo))
  (MAPENV : map_env sigma clo vs = addrs),
  CCP.map_env sigma Gamma pclo vs = addrs.
Proof with isa.
intros.
rewrite <- MAPENV.
clear MAPENV.
induction vs...
rewrite IHvs.
destruct (map_env sigma clo vs)...
cutrewrite (CCP.look_up sigma Gamma pclo a = look_up sigma clo a)...
  destruct a...
  rewrite PCLO...
Qed.

Lemma look_up_nil :
forall Gamma sigma pclo v addr
  (MAPENV : look_up sigma nil v = Some addr),
  CCP.look_up sigma Gamma pclo v = Some addr.
Proof with isa; eauto.
intros.
destruct v...
destruct n; discriminate.
Qed.

Lemma map_env_nil : 
forall sigma vs addrs
  (MAPENV : map_env sigma nil vs = Some addrs)
  Gamma pclo,
  CCP.map_env sigma Gamma pclo vs = Some addrs.
Proof with isa; try discriminate.
induction vs...
destruct addrs...
destruct (map_env sigma nil vs)...
destruct (look_up sigma nil a)...
rewrite IHvs with (addrs := addrs)...
destruct (map_env sigma nil vs)...
destruct a...
destruct (nth n sigma)...
inversion MAPENV; subst...
destruct n...
destruct (map_env sigma nil vs)...
destruct (look_up sigma nil a)...
congruence.
Qed.

Lemma make_closure_equiv : 
forall sigma (clo : addresses) Gamma pclo clo lf pe clo0
  (PCLO : Gamma pclo = Some (pe, clo))
  (MAKE : make_closure (Expr := CCP.expr) sigma clo lf = Some clo0),
  CCP.make_closure sigma Gamma pclo lf = Some clo0.
Proof with isa; eauto.
intros.
unfold make_closure in MAKE.
unfold CCP.make_closure.
destruct lf...
remember (map_env sigma clo0 v) as X.
destruct X; try discriminate.
symmetry in HeqX.
apply map_env_equiv with (Gamma := Gamma) (pe := pe) (pclo := pclo)
  in HeqX...
rewrite HeqX...
Qed.

Lemma make_closure_equiv2 : 
forall sigma (clo : addresses) Gamma pclo clo lf pe
  (PCLO : Gamma pclo = Some (pe, clo)),
  make_closure (Expr := CCP.expr) sigma clo lf =
  CCP.make_closure sigma Gamma pclo lf.
Proof with isa.
intros.
destruct lf...
cutrewrite (map_env sigma clo0 v = CCP.map_env sigma Gamma pclo v)...
induction v...
rewrite IHv...
destruct (CCP.map_env sigma Gamma pclo v)...
cutrewrite (look_up sigma clo0 a = CCP.look_up sigma Gamma pclo a)...
destruct a...
rewrite PCLO...
Qed.

Lemma make_closures_equiv : 
forall sigma (clo : addresses) Gamma pclo clo lfs pe clos
  (PCLO : Gamma pclo = Some (pe, clo))
  (MAKE : make_closures (Expr := CCP.expr) sigma clo lfs = Some clos),
  CCP.make_closures sigma Gamma pclo lfs = Some clos.
Proof with isa.
intros.
rewrite <- MAKE.
clear MAKE.
induction lfs...
rewrite IHlfs...
destruct (make_closures sigma clo0 lfs)...
erewrite <- make_closure_equiv2; eauto.
Qed.

Lemma make_closure_nil :
forall sigma clo Gamma p lf
  (MAKE : make_closure (Expr := CCP.expr) sigma nil lf = Some clo),
  CCP.make_closure sigma Gamma p lf = Some clo.
Proof with isa; eauto.
intros.
destruct lf.
unfold make_closure in MAKE.
unfold CCP.make_closure.
remember (map_env sigma nil v) as X.
symmetry in HeqX.
destruct X; try discriminate.
apply map_env_nil with (Gamma := Gamma) (pclo := p) in HeqX.
rewrite HeqX...
Qed.

Lemma make_closures_nil :
forall lfs sigma clos Gamma p
  (MAKE : make_closures (Expr := CCP.expr) sigma nil lfs = Some clos),
  CCP.make_closures sigma Gamma p lfs = Some clos.
Proof with isa; try discriminate.
induction lfs...
remember (make_closures sigma nil lfs) as mcs; symmetry in Heqmcs;
  destruct mcs...
rewrite IHlfs with (clos := g)...
remember (make_closure sigma nil a) as mc; destruct mc...
symmetry in Heqmc; eapply make_closure_nil in Heqmc.
rewrite Heqmc...
Qed.

Hint Resolve look_up_equiv map_env_equiv map_env_nil look_up_nil 
             make_closure_equiv make_closures_equiv
             make_closure_nil make_closures_nil
           : fb_ccp.

Definition heap_from_config (c : FB.config) : CU.heap :=
match c with 
| FB.Config g _ _ _ _ => g 
| FB.Enter g _ _ _ => g 
end.

Definition BH_remains (Gamma Delta : FB.heap): Prop :=
forall p pclo
  (BH   : Gamma p = Some (Black_hole, pclo)),
  Delta p = Some (Black_hole, pclo).

Lemma doesnt_touch_BH :
forall Config Value
  (EVAL : FB.Sem Config Value),
  match Value with (V, _, _) =>
    match (Config, V) with
    | (FB.Config g _ _ _ _, CU.Val_con d _ _) => BH_remains g d
    | (FB.Config g _ _ _ _, CU.Val_pap d _ _) => BH_remains g d
    | (FB.Enter g _ _ _, CU.Val_con d _ _) => BH_remains g d 
    | (FB.Enter g _ _ _, CU.Val_pap d _ _) => BH_remains g d
    end
  end.
Proof with unfold BH_remains in *; isa; eauto with fb_ccp.
intros.
induction EVAL...
(* App3 *)
destruct (eq_nat_dec p p0); subst.
rewrite BH in ONHEAP; discriminate.
unfold set.
destruct (eq_nat_dec p0 p) as [ EQ | ]...
rewrite EQ in n; tauto.
apply IHEVAL.
unfold clog.
destruct (eq_nat_dec p0 p)...
rewrite BH...
(* App4 *)
destruct Value...
destruct p0...
destruct v as [Delta0 | Delta0]; isa;
  (apply IHEVAL2; unfold set; destruct (eq_nat_dec p0 p); subst;
  [rewrite BH in ONHEAP1; discriminate | ]; apply IHEVAL1; unfold clog;
  destruct (eq_nat_dec p0 p); try rewrite BH)...
(* Let *)
destruct Value...
destruct p...
destruct v as [Delta0 | Delta0]...
apply IHEVAL...
destruct (In_dec eq_nat_dec p addrs)...
apply FRESH in i; rewrite i in BH; discriminate.
rewrite <- BH; apply alloc_nin...
apply IHEVAL...
destruct (In_dec eq_nat_dec p addrs)...
apply FRESH in i; rewrite i in BH; discriminate.
rewrite <- BH; apply alloc_nin...
(* Case_of *)
destruct Value...
destruct p...
destruct v as [Delta0 | Delta0]...
Qed.

Definition lfn_remains (Gamma Delta : FB.heap): Prop :=
forall p pclo clovars bind e
  (LFN  : Gamma p = Some (Lf_n clovars bind e, pclo)),
  Delta p = Some (Lf_n clovars bind e, pclo).

Lemma doesnt_touch_lfn :
forall Config Value
  (EVAL : FB.Sem Config Value),
  match Value with (V, _, _) =>
    match (Config, V) with
    | (FB.Config g _ _ _ _, CU.Val_con d _ _) => lfn_remains g d
    | (FB.Config g _ _ _ _, CU.Val_pap d _ _) => lfn_remains g d
    | (FB.Enter g _ _ _, CU.Val_con d _ _) => lfn_remains g d 
    | (FB.Enter g _ _ _, CU.Val_pap d _ _) => lfn_remains g d
    end
  end.
Proof with unfold lfn_remains in *; isa; eauto with fb_ccp.
intros.
induction EVAL...
(* App3 *)
destruct (eq_nat_dec p p0); subst.
rewrite LFN in ONHEAP; discriminate.
unfold set.
destruct (eq_nat_dec p0 p) as [ EQ | ]...
rewrite EQ in n; tauto.
apply IHEVAL.
unfold clog.
destruct (eq_nat_dec p0 p) as [ EQ | ]...
rewrite EQ in n0; tauto.
(* App4 *)
destruct Value...
destruct p0...
destruct v as [Delta0 | Delta0]; isa;
  (apply IHEVAL2;
  unfold set;
  destruct (eq_nat_dec p0 p); subst;
  [ rewrite LFN in ONHEAP1; discriminate
  | apply IHEVAL1; unfold clog; destruct (eq_nat_dec p0 p) as [ EQ | ];
    [ rewrite EQ in n; tauto | trivial ]]).
(* Let *)
destruct Value...
destruct p...
destruct v as [Delta0 | Delta0]...
apply IHEVAL...
destruct (In_dec eq_nat_dec p addrs)...
apply FRESH in i; rewrite i in LFN; discriminate.
rewrite <- LFN; apply alloc_nin...
apply IHEVAL...
destruct (In_dec eq_nat_dec p addrs)...
apply FRESH in i; rewrite i in LFN; discriminate.
rewrite <- LFN; apply alloc_nin...
(* Case_of *)
destruct Value...
destruct p...
destruct v as [Delta0 | Delta0]...
Qed.

Ltac exists3 a b c := exists a; exists b; exists c.
Ltac destruct3 H a b c := destruct H as [a [b [c H]]].

Lemma invariant :
forall Config Value
  (EVAL : FB.Sem Config Value),
  match Config with
  | FB.Config Gamma e sigma args clo =>
    match clo with
    | nil => forall p, CCP.Sem (CCP.Config Gamma e sigma args p) Value
    | (_::_) => forall p
      (PCLO : Gamma p = Some (Black_hole, clo)
           \/ exists clovars, exists bind, exists pe,
              Gamma p = Some (Lf_n clovars bind pe, clo)),
      CCP.Sem (CCP.Config Gamma e sigma args p) Value
    end
  | FB.Enter Gamma p args sigma =>
      CCP.Sem (CCP.Enter Gamma p args sigma) Value
  end.
Proof with isa; eauto with fb_ccp.
intros.
induction EVAL; isa; try destruct clo as [ | c cs]; isa; eauto with fb_ccp.
(* Cons *)
apply CCP.Cons; destruct PCLO...
destruct3 H clovars bind0 pe...
(* Accum *)
apply CCP.Accum with (p := p) (new_args := new_args);
  destruct PCLO...
destruct3 H clovars bind0 pe...
destruct3 H clovars bind0 pe...
(* App2 *)
eauto with fb_ccp.
apply CCP.App2 with (e := e) (bind := bind) (clo := c :: cs)
  (clovars := clovars)...
apply IHEVAL; right; exists3 clovars bind e...
(* App3 *)
apply CCP.App3 with (clovars := clovars) (e := e) (clo := c :: cs)...
apply IHEVAL with (p0 := p).
left; unfold clog.
destruct (eq_nat_dec p p); intuition...
rewrite ONHEAP...
(* App4 *)
destruct clo_e...
eapply CCP.App4...
eapply IHEVAL1...
left; unfold clog.
destruct (eq_nat_dec p p); intuition...
rewrite ONHEAP1...
(* Let *)
destruct current_clo as [ | d ds]...
apply CCP.Let with (closures := closures) (addrs := addrs);
  destruct PCLO...
destruct3 H clovars bind0 pe...
apply IHEVAL; left;
  destruct (In_dec eq_nat_dec p addrs);
  [ apply FRESH in i; rewrite H in i; discriminate
  | rewrite <- H; apply alloc_nin ]...
apply IHEVAL; right;
  destruct3 H clovars bind0 pe;
  exists3 clovars bind0 pe;
  destruct (In_dec eq_nat_dec p addrs);
  [ apply FRESH in i; rewrite H in i; discriminate
  | rewrite <- H; apply alloc_nin ]...
(* Case_of *)
apply CCP.Case_of with (bind := bind) (Delta := Delta) (e0 := e0)
  (C := C) (addrs := addrs) (theta := theta) (args0 := args0)
  (fake_bot0 := fake_bot0)...
apply IHEVAL2...
destruct PCLO...
left; assert (BH := doesnt_touch_BH _ _ EVAL1); unfold BH_remains in *...
right; destruct3 H clovars bind1 pe; exists3 clovars bind1 pe;
  assert (BH := doesnt_touch_lfn _ _ EVAL1);
  unfold lfn_remains in *...
Qed.

Lemma correctness :
forall e Value
  (FBSEM : FB.Sem (FB.Config empty_heap e nil (nil, 0) nil) Value),
  CCP.Sem (CCP.Config empty_heap e nil (nil, 0) 0) Value.
Proof.
intros.
assert (I := invariant (<< empty_heap, e, nil, (nil, 0), nil >>)
  Value FBSEM); simpl in *; auto.
Qed.
