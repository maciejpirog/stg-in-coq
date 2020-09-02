Require Import List.
Require Import ListSet.
Require Import Omega.
Require Import Arith.
Require Import Arith.Max.

(** * Compiling D to VM *)

Require Import D.
Require Import Common.
Require Import VM.

(** * Flattening terms *)

Fixpoint flatten (n : nat) (e : D.expr) {struct e}
  : nat * code_store * expr :=
match e with
| CU.App x xs (cu) => (n, nil, App x xs (cu))
| CU.Constr C xs (cu) => (n, nil, Constr C xs (cu))
| CU.Letrec lfs e => match fold_right
    (fun lf res => match lf, res with
      | Lf pi clovars bind e, (n1, cs1, vars_ptrs) =>
        match flatten n1 e with
        | (n2, cs2, fe2) => (S n2, 
            (CP_user n2, CS_lf (Lf pi clovars bind fe2)) :: cs2 ++ cs1,
            (clovars, CP_user n2) :: vars_ptrs)
        end
      end)
    (n, nil, nil) lfs with
    | (n3, cs3, vars_ptrs) => match flatten n3 e with
      | (n0, cs, fe) => (n0, cs++cs3, Letrec vars_ptrs fe)
      end
    end
| CU.Case e als => match fold_right
    (fun al res => match al, res with
      | Alt bind e0, (n0, cs0, als0) =>
        match flatten n0 e0 with
        | (n1, cs1, fe1) => (S n1,
          (CP_user n1, CS_expr fe1) :: cs1 ++ cs0,
          Alt bind (CP_user n1) :: als0)
        end
      end)
    (n, nil, nil) als with
    | (n2, cs2, als2) => match flatten n2 e with
      | (n3, cs3, fe) => (S n3, (CP_user n3, CS_alts als2) :: cs2 ++ cs3,
        Case fe (CP_user n3))
      end
    end
end.

(** * Rebuilding terms and configurations *)

Inductive Rebuild (cs : code_store) : expr -> D.expr -> Prop :=

| Reb_App : forall x xs cu,
  Rebuild cs (App x xs (cu)) (CU.App x xs (cu))

| Reb_Cons : forall C xs cu,
  Rebuild cs (Constr C xs (cu)) (CU.Constr C xs (cu))

| Reb_Letrec : forall lfs lfs0 e e_r
  (REXPR : Rebuild cs e e_r)
  (RLFS  : Rebuild_lfs cs lfs lfs0),
  Rebuild cs (Letrec lfs e) (CU.Letrec lfs0 e_r)

| Reb_Case : forall e e_r p_als als als_r
  (REXPR   : Rebuild cs e e_r)
  (FINDALS : find_cs cs p_als = CS_alts als)
  (RALS    : Rebuild_alts cs als als_r),
  Rebuild cs (Case e p_als) (CU.Case e_r als_r)

with Rebuild_lfs (cs : code_store) : list (vars * code_pointer)
  -> list D.lambda_form -> Prop :=

| Reblf_nil : Rebuild_lfs cs nil nil

| Reblf_cons : forall pi clovars bind f f_r cp lfs Dlfs
  (REBTAIL : Rebuild_lfs cs lfs Dlfs)
  (FIND    : find_cs cs cp = CS_lf (Lf pi clovars bind f))
  (REB     : Rebuild cs f f_r),
  Rebuild_lfs cs ((clovars, cp) :: lfs)
                 (Lf pi clovars bind f_r :: Dlfs)

with Rebuild_alts (cs : code_store) : alts -> D.alts -> Prop :=

| Rebal_nil : Rebuild_alts cs nil nil

| Rebal_cons : forall bind0 e e_r cp als Dals
  (REBTAIL : Rebuild_alts cs als Dals)
  (FIND    : find_cs cs cp = CS_expr e)
  (REB     : Rebuild cs e e_r),
  Rebuild_alts cs (Alt bind0 cp :: als)
                  (Alt bind0 e_r :: Dals).

Inductive Rebuild_lf (cs : code_store) : lambda_form -> D.lambda_form
  -> Prop :=
| Reb_lf : forall pi clovars bind f f_r cp
  (FIND : find_cs cs cp = CS_lf (Lf pi clovars bind f))
  (REB  : Rebuild cs f f_r),
  Rebuild_lf cs (Lf pi clovars bind f) (Lf pi clovars bind f_r).

Inductive Heap_similar (cs : code_store) : D.heap -> heap -> Prop :=
| Heap_sim : forall (Gamma : D.heap) (SGamma : heap)
  (DOM : forall x, Gamma x = None <-> SGamma x = None)
  (CLO : forall x clo1 clo2 node cp
         (C1 : Gamma x = Some (node, clo1))
         (C2 : SGamma x = Some (cp, clo2)),
         clo1 = clo2)
  (PTR : forall x clo1 clo2 cs_n ptr lf_r
         (ONHEAP1 : Gamma x = Some (Node lf_r, clo1))
         (ONHEAP2 : SGamma x = Some (ptr, clo2))
         (FIND    : find_cs cs ptr = cs_n),
         exists lf, cs_n = CS_lf lf /\ Rebuild_lf cs lf lf_r),
  Heap_similar cs Gamma SGamma.

Inductive Config_similar (cs : code_store) : D.config -> config -> Prop :=
| Config_sim_eval : forall Gamma SGamma e e_r env args pclo
  (SIMHEAP : Heap_similar cs Gamma SGamma)
  (SIMEXPR : Rebuild cs e e_r),
  Config_similar cs (CCP.Config Gamma e_r env args pclo)
                    (Config SGamma e env args pclo)

| Config_sim_enter : forall Gamma SGamma args env p
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  Config_similar cs (CCP.Enter Gamma p args env)
                    (Enter SGamma p args env).

Inductive Value_similar (cs : code_store) : D.value -> value -> Prop :=
| Value_sim_pap : forall Gamma SGamma p addrs env args
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  Value_similar cs (CU.Val_pap Gamma p addrs, env, args)
                   (Val_pap SGamma p addrs, env, args)

| Value_sim_cons : forall Gamma SGamma C addrs env args
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  Value_similar cs (CU.Val_con Gamma C addrs, env, args)
                   (Val_con SGamma C addrs, env, args).

Inductive Action_similar (cs : code_store) : D.action -> action
  -> Prop :=
| Action_sim_enter : forall C1 C2
  (SIMCONFIG : Config_similar cs C1 C2),
  Action_similar cs (D.E C1) (E C2)

| Action_sim_apply : forall V1 V2
  (SIMVALUE : Value_similar cs V1 V2),
  Action_similar cs (D.A V1) (A V2).

Inductive Stack_similar (cs : code_store) : D.stack -> stack -> Prop :=

| Stack_sim_nil : Stack_similar cs nil nil

| Stack_sim_upd : forall a b p fb
  (SS : Stack_similar cs a b),
  Stack_similar cs (D.K_upd p fb :: a) (K_upd p fb :: b)

| Stack_sim_alt : forall a b cp als als_r fb
  (FIND : find_cs cs cp = CS_alts als)
  (HS   : Rebuild_alts cs als als_r)
  (SS   : Stack_similar cs a b),
  Stack_similar cs (D.K_alt als_r fb  :: a) (K_alt cp fb :: b).

Inductive Similar (cs : code_store) : D.action * D.stack
  -> action * stack -> Prop :=

| Sim : forall A DA K DK
  (SIMACTION : Action_similar cs DA A)
  (SIMSTACK  : Stack_similar cs DK K),
  Similar cs (DA, DK) (A, K).

Inductive Similar_clo : code_store -> closure
  -> gen_closure (Expr := D.expr) -> Prop :=

| Sim_clo : forall cs addrs lf_fla lf cp
  (FINDCS : find_cs cs cp = CS_lf lf_fla)
  (REBLF  : Rebuild_lf cs lf_fla lf),
  Similar_clo cs (cp, addrs) (Node lf, addrs)

| Sim_clo_bh : forall cs addrs cp,
  Similar_clo cs (cp, addrs) (Black_hole, addrs).

Inductive Similar_clos : code_store -> closures
  -> gen_closures (Expr := D.expr) -> Prop :=

| Sim_clos_nil : forall cs, Similar_clos cs nil nil

| Sim_clos_cons : forall cs clos Dclos clo Dclo
  (HEAD : Similar_clo cs clo Dclo)
  (TAIL : Similar_clos cs clos Dclos),
  Similar_clos cs (clo :: clos) (Dclo :: Dclos).

Hint Constructors Sem D.Sem Stack_similar Action_similar Value_similar
                  Config_similar Heap_similar Rebuild_lf Rebuild
                  Similar.

Lemma elem_similar :
forall cs Gamma SGamma p pi clovars bind0 e_r some_clo
  (HEAPSIM : Heap_similar cs Gamma SGamma)
  (ELEM    : Gamma p = Some (Node (Lf pi clovars bind0 e_r), some_clo)),
  exists cp, exists e,
  SGamma p = Some (cp, some_clo) /\
  find_cs cs cp = CS_lf (Lf pi clovars bind0 e) /\
  Rebuild cs e e_r.
Proof with isa.
intros.
inversion HEAPSIM; subst.
remember (SGamma p) as H.
destruct H.
symmetry in HeqH; destruct c as [cp addrs].
remember HeqH as H1; clear HeqH1; apply CLO with (clo1 := some_clo)
  (node0 := Node (Lf pi clovars bind0 e_r)) in H1; subst...
exists cp.
remember HeqH as H; clear HeqH0.
apply PTR with (clo1 := addrs) (cs_n := find_cs cs cp)
  (lf_r := Lf pi clovars bind0 e_r) in H...
destruct H as [lf [FIND REBUILD]].
inversion REBUILD; subst.
exists f...
symmetry in HeqH.
apply <- DOM in HeqH.
rewrite HeqH in *; discriminate.
Qed.

Lemma clog_similar :
forall cs Gamma p SGamma
  (SIMILAR : Heap_similar cs Gamma SGamma),
  Heap_similar cs (clog Gamma p) SGamma.
Proof with isa.
intros.
inversion SIMILAR; subst.
constructor...
unfold clog.
destruct (eq_nat_dec x p) as [EQ | NEQ]; subst...
split...
remember (Gamma p) as G.
destruct G...
destruct c; discriminate.
apply -> DOM...
apply <- DOM in H; rewrite H...
unfold clog in C1.
destruct (eq_nat_dec x p) as [EQ | NEQ]; subst...
remember (Gamma p) as G.
destruct G; try discriminate...
destruct c.
inversion C1; subst.
symmetry in HeqG.
eapply CLO; eauto.
eapply CLO; eauto.
unfold clog in ONHEAP1.
destruct (eq_nat_dec x p) as [EQ | NEQ]; subst...
remember (Gamma p) as G.
destruct G; try discriminate...
destruct c.
inversion ONHEAP1; subst; discriminate.
eapply PTR; eauto.
Qed.

(** * Statistics *)

Definition app_stat := nat.

Definition cons_stat := ListSet.set (constructor * nat).

Definition statistics := (app_stat * cons_stat)%type.

Definition cons_times_nat_eq_dec : forall a b : constructor * nat,
  {a = b} + {a <> b}.
Proof.
decide equality.
Qed.

Definition cons_stat_eq_dec : forall a b : cons_stat, {a = b} + {a <> b}.
Proof.
apply list_eq_dec.
apply cons_times_nat_eq_dec.
Qed.

(** * Upper bounds *)

Inductive UB (* upper bound *) : statistics -> expr -> Prop :=

| UB_App : forall stat x xs cu,
  UB stat (App x xs cu)

| UB_Cons : forall stat_app stat_cons C xs cu
  (INSTAT : set_In (C, length xs) stat_cons),
  UB (stat_app, stat_cons) (Constr C xs cu)

| UB_Letrec : forall stat lfs e
  (UBEXPR : UB stat e),
  UB stat (Letrec lfs e)

| UB_Case : forall stat cp e
  (UBEXPR : UB stat e),
  UB stat (Case e cp).

Inductive UB_lf : statistics -> lambda_form -> Prop :=

| UBlf : forall stat_app stat_cons pi clovars bind e
  (UBEXPR : UB (stat_app, stat_cons) e)
  (BIND   : bind <= stat_app),
  UB_lf (stat_app, stat_cons) (Lf pi clovars bind e).

Inductive UB_csn : statistics -> cs_node -> Prop :=

| UBcsn_expr : forall stat e
  (UBEXPR : UB stat e),
  UB_csn stat (CS_expr e)

| UBcsn_lf : forall stat lf
  (UBLF : UB_lf stat lf),
  UB_csn stat (CS_lf lf)

| UBcsn_alts : forall stat als,
  UB_csn stat (CS_alts als)

| UBcsn_none : forall stat,
  UB_csn stat (CS_None).

Inductive UB_cs : statistics -> code_store -> Prop :=

| UBcs : forall stat cs
  (UBIN : forall csn cp
          (FINDCS : find_cs cs cp = csn),
          UB_csn stat csn),
  UB_cs stat cs.

Inductive UB_conf : statistics -> action * stack -> Prop :=

| UBconf_conf : forall stat e Gamma sigma args clo stack
  (UBEXPR : UB stat e),
  UB_conf stat (E (Config Gamma e sigma args clo), stack)

| UBconf_enter : forall stat Gamma a args clo stack,
  UB_conf stat (E (Enter Gamma a args clo), stack)

| UB_conf_apply_pap : forall stat_app stat_cons Gamma q addrs theta
  args stack
  (UBLEN : length addrs <= stat_app),
  UB_conf (stat_app, stat_cons)
    (A (Val_pap Gamma q addrs, theta, args), stack)

| UB_conf_apply_cons : forall stat_app stat_cons Gamma C addrs theta
  args stack
  (UBCONS : set_In (C, length addrs) stat_cons),
  UB_conf (stat_app, stat_cons)
    (A (Val_con Gamma C addrs, theta, args), stack).

Hint Constructors UB UB_lf UB_csn UB_cs UB_conf.

Notation " a <# b " := (set_subset (constructor * nat) a b) (at level 40).

Hint Resolve set_subset_refl set_subset_union1 set_subset_union2.

Lemma UB_weaken : forall spap sPAP scons sCONS
  (LE     : spap <= sPAP)
  (SUBSET : scons <# sCONS)
  e
  (UBS    : UB (spap, scons) e),
  UB (sPAP, sCONS) e.
Proof with isa.
intros.
induction e; constructor; inversion UBS; subst...
Qed.

Hint Resolve UB_weaken.

Lemma UB_csn_weaken : forall spap sPAP scons sCONS
  (LE     : spap <= sPAP)
  (SUBSET : scons <# sCONS)
  csn
  (UBS    : UB_csn (spap, scons) csn),
  UB_csn (sPAP, sCONS) csn.
Proof with isa; eauto.
intros.
destruct csn...
(* expr *)
inversion UBS; subst...
(* lf *)
destruct l; subst.
inversion UBS; subst.
constructor.
inversion UBLF; subst.
constructor...
omega.
Qed.

Hint Resolve UB_csn_weaken.

Lemma UB_cs_weaken : forall spap sPAP scons sCONS
  (LE     : spap <= sPAP)
  (SUBSET : scons <# sCONS)
  cs
  (UBS    : UB_cs (spap, scons) cs),
  UB_cs (sPAP, sCONS) cs.
Proof with isa; eauto.
intros.
constructor.
intros.
inversion UBS; subst.
apply UB_csn_weaken with (spap := spap) (scons := scons)...
Qed.

Hint Resolve UB_csn_weaken.

Lemma find_cs_app3 :
forall cs1 cs2 cp csn
  (FINDCS : find_cs (cs1 ++ cs2) cp = csn),
  find_cs cs1 cp = csn \/ find_cs cs2 cp = csn.
Proof with isa.
induction cs1...
destruct a.
destruct eq_cp_dec; subst...
Qed.

Lemma UB_cs_app :
forall stats cs1 cs2
  (NOTEMPTY : forall cp csn (IN : In (cp, csn) cs1), csn <> CS_None)
  (UBCS1 : UB_cs stats cs1)
  (UBCS2 : UB_cs stats cs2),
  UB_cs stats (cs1 ++ cs2).
Proof with isa.
intros.
inversion UBCS1; inversion UBCS2; subst.
constructor...
apply find_cs_app3 in FINDCS.
destruct FINDCS; eauto.
Qed.

Definition gather_stats : forall e, {stat | UB stat e}.
Proof with intros; simpl; auto.
induction e.
exists (length v0, nil)...
exists (0, (c, length v) :: nil); constructor...
destruct IHe as [stat UBe]; exists stat...
destruct IHe as [stat UBe]; exists stat...
Qed.

Definition gather_stats_csn : forall csn, {stat | UB_csn stat csn}.
Proof with isa; auto with arith.
destruct csn...
destruct (gather_stats e) as [s UBe]; exists s...
exists (0, nil)...
destruct l.
destruct (gather_stats e) as [s UBe]; destruct s as [spap scons];
  exists (max spap b, scons).
constructor; constructor...
apply UB_weaken with (spap := spap) (scons := scons)...
exists (0, nil)...
Qed.

Definition stat_sum (a b : statistics) : statistics :=
match a, b with
| (apap, acons), (bpap, bcons) =>
  (max apap bpap, set_union cons_times_nat_eq_dec acons bcons)
end.

Definition gather_stats_cs : forall cs, {stat | UB_cs stat cs}.
Proof with isa; auto with arith.
induction cs.
(* nil *)
exists (0, nil); constructor...
subst...
(* cons *)
destruct IHcs as [Xstat_cs XUB_cs].
destruct a as [cp csn].
destruct (gather_stats_csn csn) as [Xstat_node XUB_node].
exists (stat_sum Xstat_node Xstat_cs)...
unfold stat_sum...
destruct Xstat_node as [node_pap node_cons].
destruct Xstat_cs as [cs_pap cs_cons].
constructor...
destruct eq_cp_dec; subst.
apply UB_csn_weaken with (spap := node_pap) (scons := node_cons)...
apply UB_csn_weaken with (spap := cs_pap) (scons := cs_cons)...
inversion XUB_cs; subst; apply UBIN with (cp := cp0)...
Qed.

Inductive Implements : code_store -> statistics -> Prop :=

| Impl : forall stat_app stat_cons cs
  (APP  : forall n
          (LEQ : n <= stat_app),
          find_cs cs (CP_pap n) = CS_lf
            (Lf Dont_update nil 0 (App (C_ind 0)
            (map C_ind (from 1 n)) 0)))
  (CONS : forall C n
          (INSTAT : set_In (C, n) stat_cons),
          find_cs cs (CP_cons C n) = CS_lf
            (Lf Dont_update nil 0 (Constr C (map C_ind (from 0 n)) 0))),
  Implements cs (stat_app, stat_cons).

Fixpoint impl_for_pap (n : app_stat) : code_store :=
match n with
| O => (CP_pap 0, CS_lf (Lf Dont_update nil 0 (App (C_ind 0)
         (map C_ind (from 1 0)) 0))) :: nil
| S m => (CP_pap n, CS_lf (Lf Dont_update nil 0 (App (C_ind 0)
            (map C_ind (from 1 n)) 0))) :: impl_for_pap m
end.

Fixpoint impl_for_cons (xs : cons_stat) : code_store :=
match xs with
| (C, n) :: xs0 => (CP_cons C n, CS_lf
      (Lf Dont_update nil 0 (Constr C (map C_ind (from 0 n)) 0)))
      :: impl_for_cons xs0
| nil => nil
end.

Lemma find_cs_app :
forall cs cs0 cp node
  (FINDAPP : find_cs cs cp = CS_lf node),
  find_cs (cs ++ cs0) cp = CS_lf node.
Proof with isa.
induction cs...
discriminate.
destruct a.
destruct (eq_cp_dec cp c); subst...
Qed.

Lemma find_cs_app2 :
forall cs1 cp
  (FINDAPP1 : find_cs cs1 cp = CS_None)
  (NOTEMPTY : forall cp csn (IN : In (cp, csn) cs1), csn <> CS_None)
  cs2 node
  (FINDAPP2 : find_cs cs2 cp = CS_lf node),
  find_cs (cs1 ++ cs2) cp = CS_lf node.
Proof with isa.
intros.
induction cs1...
destruct a.
destruct (eq_cp_dec cp c); subst.
assert (X := NOTEMPTY c CS_None (or_introl _ (refl_equal _))); tauto.
eauto.
Qed.

Lemma impl_for_implement :
forall stat_app stat_cons cs,
  Implements (impl_for_pap stat_app ++ impl_for_cons stat_cons ++ cs)
    (stat_app, stat_cons).
Proof with isa.
intros.
constructor...
(* pap *)
apply find_cs_app.
induction LEQ.
destruct n.
unfold impl_for_pap.
unfold find_cs.
destruct (eq_cp_dec (CP_pap 0) (CP_pap 0))...
tauto.
unfold impl_for_pap.
unfold find_cs.
destruct (eq_cp_dec (CP_pap (S n)) (CP_pap (S n)))...
tauto.
unfold impl_for_pap.
unfold find_cs.
destruct (eq_cp_dec (CP_pap n) (CP_pap (S m)))...
inversion e.
tauto.
(* cons *)
apply find_cs_app2.
induction stat_app...
induction stat_app...
  inversion IN.
  inversion H; subst.
  intro; discriminate.
  contradiction.
  inversion IN; eauto.
  inversion H; intro; discriminate.
apply find_cs_app.
induction stat_cons; inversion INSTAT.
destruct a; inversion H; subst; clear H.
unfold impl_for_cons.
unfold find_cs.
destruct (eq_cp_dec (CP_cons C n) (CP_cons C n))...
tauto.
unfold impl_for_cons.
destruct a.
unfold find_cs.
destruct (eq_cp_dec (CP_cons C n) (CP_cons c n0))...
inversion e...
Qed.

Lemma cs_induction :
forall cs (P : cs_node -> Prop)
  (IN   : forall cp csn
          (INCS : In (cp, csn) cs),
          P csn)
  (NONE : P CS_None)
  cp csn
  (FIND : find_cs cs cp = csn),
  P csn.
Proof with isa.
intros.
induction cs...
subst...
destruct a; destruct eq_cp_dec; subst.
apply (IN c csn (or_introl _ (refl_equal _))).
eauto.
Qed.

Lemma impl_for_UB :
forall stat_app stat_cons cs
  (UBCS : UB_cs (stat_app, stat_cons) cs),
  UB_cs (stat_app, stat_cons)
    (impl_for_pap stat_app ++ impl_for_cons stat_cons ++ cs).
Proof with isa.
intros.
apply UB_cs_app...
(* *)
clear UBCS; induction stat_app...
destruct IN as [IN | IN]; inversion IN; subst; intro; discriminate...
destruct IN as [IN | IN].
inversion IN; subst; intro; discriminate.
apply IHstat_app...
(* *)
clear UBCS.
constructor...
apply cs_induction with (P := UB_csn (stat_app, stat_cons)) in FINDCS...
clear FINDCS.
induction stat_app...
destruct INCS; inversion H; subst...
destruct INCS.
inversion H; subst; constructor; constructor; constructor; auto with arith.
apply UB_csn_weaken with (spap := stat_app) (scons := stat_cons)...
(* *)
apply UB_cs_app...
clear UBCS; induction stat_cons...
destruct a...
destruct IN...
inversion H; subst; intro; discriminate.
(* *)
clear UBCS.
constructor...
apply cs_induction with (P := UB_csn (stat_app, stat_cons)) in FINDCS...
clear FINDCS.
induction stat_cons...
contradiction.
destruct a.
destruct INCS.
inversion H; subst.
constructor; constructor; try constructor; auto with arith.
rewrite map_length; rewrite from_length...
apply UB_csn_weaken with (spap := stat_app) (scons := stat_cons)...
unfold set_subset...
Qed.

Lemma length_firstn :
forall (T : Type) (n : nat) (xs : list T),
  length (firstn n xs) <= n.
Proof with isa.
induction n...
induction xs...
auto with arith.
auto with arith.
Qed.

Lemma len_firstn_minus :
forall (T : Type) (xs : list T) (n : nat),
  length (firstn (length xs - n) xs) <= length xs - n.
Proof with isa.
induction xs...
destruct n...
assert (IHxs2 := IHxs O).
rewrite <- minus_n_O in *; auto with arith.
apply length_firstn.
Qed.

Lemma map_env_length :
forall sigma Gamma pclo xs addrs
  (MAPENV : CCP.map_env sigma Gamma pclo xs = Some addrs),
  length xs = length addrs.
Proof with isa.
intros ? ? ? ?.
induction xs...
inversion MAPENV...
induction addrs...
destruct (CCP.map_env sigma Gamma pclo xs); try discriminate.
destruct (CCP.look_up sigma Gamma pclo a); try discriminate.
f_equal.
apply IHxs.
remember (CCP.map_env sigma Gamma pclo xs) as ME;
  destruct ME; try discriminate.
remember (CCP.look_up sigma Gamma pclo a) as LU;
  destruct LU; try discriminate...
congruence.
Qed.

Lemma set_none :
forall Gamma SGamma cs p c d x
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  Common.set Gamma p c x = None <->
  set SGamma p d x = None.
Proof with isa.
intros.
unfold set.
unfold Common.set.
destruct (eq_nat_dec x p); subst.
split; intro; discriminate.
inversion SIMHEAP; subst...
Qed.

Lemma set_con_clo_eq :
forall cs Gamma SGamma p C addrs x node0 cp clo1 clo2
  (SIMHEAP : Heap_similar cs Gamma SGamma)
  (C1 : Common.set Gamma p (CU.make_cons C addrs) x = Some (node0, clo1))
  (C2 : set SGamma p (CP_cons C (length addrs), addrs) x =
    Some (cp, clo2)),
  clo1 = clo2.
Proof with isa.
intros.
unfold set in *.
unfold Common.set in *.
destruct (eq_nat_dec x p); subst.
unfold CU.make_pap in C1.
inversion C1; subst.
inversion C2; subst...
destruct node0.
destruct g.
assert (X := elem_similar _ _ _ _ _ _ _ _ _ SIMHEAP C1).
destruct X as [X1 [X2 [X3]]].
congruence.
inversion SIMHEAP; subst.
eapply CLO; eauto.
Qed.

Lemma set_pap_clo_eq :
forall cs Gamma SGamma p q addrs x node0 cp clo1 clo2
  (SIMHEAP : Heap_similar cs Gamma SGamma)
  (C1 : Common.set Gamma p (CU.make_pap q addrs) x = Some (node0, clo1))
  (C2 : set SGamma p (CP_pap (length addrs), q :: addrs) x =
    Some (cp, clo2)),
  clo1 = clo2.
Proof with isa.
intros.
unfold set in *.
unfold Common.set in *.
destruct (eq_nat_dec x p); subst.
unfold CU.make_pap in C1.
inversion C1; subst.
inversion C2; subst...
destruct node0.
destruct g.
assert (X := elem_similar _ _ _ _ _ _ _ _ _ SIMHEAP C1).
destruct X as [X1 [X2 [X3]]].
congruence.
inversion SIMHEAP; subst.
eapply CLO; eauto.
Qed.

Lemma sim_select_case :
forall C cs alts0 als e0 bind0
  (HS : Rebuild_alts cs alts0 als)
  (SELECT : nth C als = Some (Alt bind0 e0)),
  exists p_e : code_pointer, exists e : expr,
  nth C alts0 = Some (Alt bind0 p_e) /\ find_cs cs p_e = CS_expr e /\
  Rebuild cs e e0.
Proof with isa.
induction C...
destruct als...
discriminate.
inversion HS; subst...
inversion SELECT; subst...
exists cp.
exists e...
destruct als...
discriminate.
destruct alts0...
inversion HS...
inversion HS; subst...
eapply IHC; eauto.
Qed.

Lemma look_up_similar :
forall cs Gamma SGamma sigma pclo x
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  CCP.look_up sigma Gamma pclo x = look_up sigma SGamma pclo x.
Proof with isa.
intros.
destruct x...
inversion SIMHEAP; subst.
clear PTR.
remember (SGamma pclo) as SGp.
remember (Gamma pclo) as Gp.
destruct SGp.
destruct c.
destruct Gp.
destruct c0...
assert (a0 = a); [ intuition eauto | subst ]...
symmetry in HeqGp; apply DOM in HeqGp; congruence.
destruct Gp...
destruct c...
symmetry in HeqSGp; apply DOM in HeqSGp; congruence.
Qed.

Lemma map_env_similar :
forall cs Gamma SGamma sigma xs pclo addrs
  (SIMHEAP : Heap_similar cs Gamma SGamma)
  (MAPENV : CCP.map_env sigma Gamma pclo xs = Some addrs),
  map_env sigma SGamma pclo xs = Some addrs.
Proof with isa.
intros.
rewrite <- MAPENV.
clear addrs MAPENV.
inversion SIMHEAP; subst.
clear PTR.
induction xs...
rewrite IHxs...
remember (CCP.map_env sigma Gamma pclo xs) as me.
destruct me...
rewrite (look_up_similar cs Gamma SGamma)...
Qed.

Lemma make_closure_similar :
forall cs sigma Gamma SGamma pclo lf clo lf_fla cp
  (REBLF   : Rebuild_lf cs lf_fla lf)
  (FINDCS  : find_cs cs cp = CS_lf lf_fla)
  (CLO     : CCP.make_closure sigma Gamma pclo lf = Some clo)
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  exists clo_fla,
  match lf with Lf _ clovars _ _ =>
    make_closure sigma SGamma pclo (clovars, cp) = Some clo_fla /\
    Similar_clo cs clo_fla clo
  end.
Proof with isa.
intros.
destruct lf as [pi clovars bind0 f].
remember (make_closure sigma SGamma pclo (clovars, cp)) as mc.
  destruct mc; symmetry in Heqmc.
exists c.
split...
destruct c as [cp_c addrs_c].
destruct clo as [[lf_clo | ] addrs_clo].
cutrewrite (addrs_clo = addrs_c).
cutrewrite (cp_c = cp).
eapply Sim_clo; eauto.
cutrewrite (lf_clo = Lf pi clovars bind0 f)...
destruct (CCP.map_env sigma Gamma pclo clovars); inversion CLO...
destruct (map_env sigma SGamma pclo clovars); inversion Heqmc...
remember (CCP.map_env sigma Gamma pclo clovars) as CCPME.
destruct CCPME; try discriminate.
symmetry in HeqCCPME.
apply map_env_similar with (cs := cs) (SGamma := SGamma) in HeqCCPME...
rewrite HeqCCPME in *; congruence.
cutrewrite (addrs_clo = addrs_c).
apply Sim_clo_bh.
remember (CCP.map_env sigma Gamma pclo clovars) as CCPME.
destruct CCPME; try discriminate.
symmetry in Heqmc.
unfold CCP.make_closure in *.
unfold make_closure in *.
remember (CCP.map_env sigma Gamma pclo clovars) as menv; destruct menv;
  try discriminate; symmetry in Heqmenv.
assert (MES := map_env_similar _ _ _ _ _ _ _ SIMHEAP Heqmenv).
rewrite MES in Heqmc; discriminate.
Qed.

(** The following lemma is as silly as its name. Look for the place
tagged "?!?" in the proof of the "make_closures_similar" lemma
for details. *)

Lemma xx :
forall sigma Gamma pclo pi clovars bind0 f_r g clos 
(MC : option gen_closure)
(HeqMC : MC = CCP.make_closure (Expr := D.expr) sigma Gamma pclo (Lf pi clovars bind0 f_r))
(CLOS : match CCP.make_closure sigma Gamma pclo (Lf pi clovars bind0 f_r) with
       | Some clo => Some (clo :: g)
       | None => None
       end = Some clos),
match MC with
       | Some clo => Some (clo :: g)
       | None => None
       end = Some clos.
Proof with isa.
intros.
rewrite <- HeqMC in CLOS...
Qed.

Lemma make_closures_similar :
forall cs lfs lfs_fla sigma Gamma SGamma pclo clos
  (REBLFS : Rebuild_lfs cs lfs_fla lfs)
  (CLOS   : CCP.make_closures sigma Gamma pclo lfs = Some clos)
  (SIMHEAP : Heap_similar cs Gamma SGamma),
  exists clos_fla,
  make_closures sigma SGamma pclo lfs_fla = Some clos_fla /\
    Similar_clos cs clos_fla clos.
Proof with isa.
induction lfs...
(* nil *)
destruct clos; try discriminate.
exists nil.
split...
inversion REBLFS; subst...
constructor.
(* cons *)
destruct lfs_fla; inversion REBLFS; subst.
remember (CCP.make_closures sigma Gamma pclo lfs) as MCS;
  destruct MCS; try discriminate.
remember (CCP.make_closure (Expr := D.expr) sigma Gamma pclo
  (Lf pi clovars bind f_r)) as MC.
(* rewrite <- HeqMC in CLOS.   <--- !?! *)
apply xx with (MC := MC) in CLOS.
destruct MC; inversion CLOS; subst; clear CLOS.
symmetry in HeqMC.
apply make_closure_similar with (cs := cs) (SGamma := SGamma)
  (lf_fla := Lf pi clovars bind f) (cp := cp) in HeqMC...
destruct HeqMC as [clo_fla [H H0]].
symmetry in HeqMCS.
destruct (IHlfs _ _ _ _ _ _ REBTAIL HeqMCS SIMHEAP) as [clos_fla [HS H0S]].
exists (clo_fla :: clos_fla)...
rewrite HS...
rewrite H...
split...
constructor...
inversion REBLFS; subst...
econstructor; eauto.
trivial.
Qed.

Lemma make_clos_length :
forall sigma Gamma pclo lfs closures0
  (CLOS : CCP.make_closures (Expr := D.expr) sigma Gamma pclo lfs = Some closures0),
  length lfs = length closures0.
Proof with isa.
induction lfs; destruct closures0...
inversion CLOS.
destruct (CCP.make_closures sigma Gamma pclo lfs);
  destruct (CCP.make_closure sigma Gamma pclo a); try congruence.
f_equal...
apply IHlfs...
remember (CCP.make_closures sigma Gamma pclo lfs) as MCS.
destruct MCS; try discriminate.
destruct (CCP.make_closure sigma Gamma pclo a); inversion CLOS...
Qed.

Lemma make_clos_length2 :
forall sigma Gamma pclo lfs closures0
  (CLOS : make_closures sigma Gamma pclo lfs = Some closures0),
  length lfs = length closures0.
Proof with isa.
induction lfs; destruct closures0...
inversion CLOS.
destruct (make_closures sigma Gamma pclo lfs);
  destruct (make_closure sigma Gamma pclo a); try congruence.
f_equal...
apply IHlfs...
remember (make_closures sigma Gamma pclo lfs) as MCS.
destruct MCS; try discriminate.
destruct (make_closure sigma Gamma pclo a); inversion CLOS...
Qed.

Lemma rebuild_lfs_length :
forall cs lfs0 lfs
  (RLFS : Rebuild_lfs cs lfs0 lfs),
  length lfs0 = length lfs.
Proof with isa.
intros.
induction RLFS...
Qed.

(* *)

Lemma invariant :
forall cs DConf DVal stat
  (UB_IMPL : Implements cs stat)
  (UB_CS   : UB_cs stat cs)
  (DEVAL   : D.Sem DConf DVal)
  Conf
  (UB_CONF : UB_conf stat Conf)
  (SIMILAR : Similar cs DConf Conf),
  exists Val, Sem cs Conf Val /\ Value_similar cs DVal Val.
Proof with isa; try discriminate.
intros ? ? ? ? ? ? ?.
induction DEVAL...
(* Halt *)
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMSTACK; subst.
exists V2...
(* Cons *)
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
inversion SIMEXPR; subst.
destruct IHDEVAL with (Conf := (A (Val_con SGamma C addrs,
  skipn cleanup sigma, (args, length args)), K0)) as [Val [RED SIM]]...
  destruct stat as [stat_app stat_cons]; apply UB_conf_apply_cons.
  inversion UB_CONF; subst.
  inversion UBEXPR; subst.
  apply map_env_length in MAPENV; rewrite <- MAPENV...
exists Val; split...
apply Cons with (addrs := addrs)...
erewrite map_env_similar; eauto.
(* Accum *)
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
inversion SIMEXPR; subst.
remember (E (Enter SGamma p (new_args++args, fake_bot)
  (skipn cleanup sigma)), K0) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]].
  subst; constructor...
subst; exists Val; split...
apply Accum with (p := p) (new_args := new_args)...
erewrite map_env_similar; eauto.
erewrite <- look_up_similar; eauto.
(* App1 *)
rename e into f_r.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
destruct IHDEVAL with (Conf := (A
  (Val_pap SGamma p (firstn (length args - fake_bot) args),
  sigma, (skipn (length args - fake_bot) args, fake_bot)), K0))
  as [Val [RED SIM]]...
  destruct stat as [stat_app stat_cons]; constructor.
  destruct (elem_similar _ _ _ _ _ _ _ _ _ SIMHEAP ONHEAP)
    as [cp [e [ELEM [FINDCS REB]]]].
  inversion UB_CS; subst.
  assert (UBIN2 := UBIN _ _ FINDCS).
  inversion UBIN2; subst.
  inversion UBLF; subst.
  assert (L := lt_le_trans _ _ _ LENGTH BIND).
  apply lt_le_weak.
  apply le_lt_trans with (m := length args - fake_bot)...
apply len_firstn_minus.
exists Val; split...
apply elem_similar with (cs := cs) (SGamma := SGamma) in ONHEAP;
  destruct ONHEAP as [cp [f [ONHEAP [FIND REBUILD]]]]...
eapply App1; [ apply FIND | apply ONHEAP | reflexivity | reflexivity |
  trivial | trivial ].
(* App2 *)
rename e into f_r.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
apply elem_similar with (cs := cs) (SGamma := SGamma) in ONHEAP;
  destruct ONHEAP as [cp [f [ONHEAP [FIND REBUILD]]]]...
remember (E (Config SGamma f (firstn bind args ++ sigma)
  (skipn bind args, fake_bot) p), K0) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
  inversion UB_CS; subst.
  assert (UBIN2 := UBIN _ _ FIND).
  inversion UBIN2.
  inversion UBLF; subst...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
exists Val; split...
eapply App2; eauto.
(* App_Eval *)
rename e into f_r.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
apply elem_similar with (cs := cs) (SGamma := SGamma) in ONHEAP1;
  destruct ONHEAP1 as [cp [f [ONHEAP [FIND REBUILD]]]]...
remember (E (Config SGamma f sigma
  (args, length args) p), K_upd p fake_bot :: K0) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
  inversion UB_CS; subst.
  assert (UBIN2 := UBIN _ _ FIND).
  inversion UBIN2.
  inversion UBLF; subst...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
  constructor...
  constructor...
  constructor...
  apply clog_similar...
exists Val; split...
eapply App_Eval; eauto.
(* App3 *)
rename Delta into Gamma.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMVALUE; subst.
inversion SIMSTACK as [ | K1 SS1 | ]; subst...
remember (A
  (Val_con (set SGamma p (CP_cons C (length addrs), addrs)) C addrs,
  theta, (args, length args)), SS1) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; destruct stat as [stat_app stat_cons].
  apply UB_conf_apply_cons.
  inversion UB_CONF; subst...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
  constructor...
  constructor...
  constructor...
  constructor...
  eapply set_none; eauto.
  eapply set_con_clo_eq; eauto.
  unfold set in *.
  unfold Common.set in *.
  destruct (eq_nat_dec x p)...
  (* *) subst.
  inversion ONHEAP1; subst.
  inversion ONHEAP2; subst.
  inversion UB_IMPL; subst.
  clear APP IHDEVAL ONHEAP2.
  inversion UB_CONF; subst.
  assert (CONS2 := CONS _ _ UBCONS).
  exists (Lf Dont_update nil 0
    (Constr C (map C_ind (from 0 (length clo2))) 0)).
  split...
  econstructor...
  (* *) inversion SIMHEAP; subst; eapply PTR; eauto.
exists Val; split...
(* App4 *)
rename Delta into Gamma.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMVALUE; subst.
inversion SIMSTACK as [ | K1 SS1 | ]; subst...
destruct IHDEVAL with (Conf := (E
  (Enter (set SGamma p (CP_pap (length addrs), q :: addrs)) q
  (addrs ++ args0, fake_bot) theta), SS1))
  as [Val [RED SIM]]...
  constructor...
  constructor...
  constructor...
  constructor...
  eapply set_none; eauto.
  eapply set_pap_clo_eq; eauto.
  unfold set in *.
  unfold Common.set in *.
  destruct (eq_nat_dec x p)...
  (* *) subst.
  inversion ONHEAP1; subst.
  inversion ONHEAP2; subst.
  inversion UB_IMPL; subst.
  clear CONS IHDEVAL ONHEAP2.
  inversion UB_CONF; subst.
  assert (APP2 := APP _ UBLEN).
  exists (Lf Dont_update nil 0
    (App (C_ind 0) (map C_ind (from 1 (length addrs))) 0)).
  split...
  econstructor...
  (* *) inversion SIMHEAP; subst; eapply PTR; eauto.
exists Val.
split...
(* Let *)
assert (LALC : length addrs = length closures).
  erewrite <- make_clos_length; eauto.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
inversion SIMEXPR; subst.
destruct (make_closures_similar _ _ _ _ _ _ _ _ RLFS CLOS SIMHEAP)
  as [clos_fla [H H0]].
remember (E (Config (alloc SGamma addrs clos_fla) e1
  (addrs ++ sigma) args pclo), K0) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
  inversion UB_CONF; subst.
  inversion UBEXPR...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
  constructor...
  constructor...
  constructor...
  constructor...
  (* *) destruct (In_dec eq_nat_dec x addrs) as [IN | NIN].
  destruct (Common.alloc_some _ Gamma x addrs closures)...
  destruct (alloc_some SGamma x addrs clos_fla)...
  rewrite LENGTH.
  erewrite <- make_clos_length2; eauto.
  symmetry; eapply rebuild_lfs_length; eauto.
  split; congruence.
  rewrite (Common.alloc_nin _ Gamma addrs)...
  rewrite (alloc_nin SGamma addrs)...
  inversion SIMHEAP...
  (* *) destruct (In_dec eq_nat_dec x addrs) as [ IN | NIN ].
  clear FRESH CLOS DEVAL IHDEVAL K K0 SIMSTACK REXPR SIMEXPR
    SIMACTION UB_CONF UB_CONF2 SIMILAR e e1 SIMCONFIG
    UB_IMPL UB_CS H.
  generalize dependent addrs.
  generalize dependent lfs.
  generalize dependent lfs0.
  induction H0...
  destruct addrs; isa; [ contradiction | discriminate ].
  destruct addrs; try discriminate...
  destruct lfs; try discriminate...
  destruct (eq_nat_dec a x); subst.
  unfold alloc in C2; unfold Common.alloc in C1...
  unfold set in C2; unfold Common.set in C1...
  destruct eq_nat_dec; try tauto...
  inversion HEAD; subst; congruence.
  destruct IN as [ | IN ]; try tauto.
  unfold alloc in C2; unfold Common.alloc in C1...
  unfold set in C2; unfold Common.set in C1...
  destruct (eq_nat_dec x a); subst; try tauto...
  destruct lfs0; inversion RLFS; subst.
  apply IHSimilar_clos with (lfs0 := lfs0) (lfs := lfs)
    (addrs := addrs)...
  rewrite (Common.alloc_nin _ Gamma addrs) in C1...
  rewrite (alloc_nin SGamma addrs) in C2...
  inversion SIMHEAP; subst; eauto.
  (* *) destruct (In_dec eq_nat_dec x addrs) as [ IN | NIN ].
  clear FRESH CLOS DEVAL IHDEVAL K K0 SIMSTACK REXPR SIMEXPR
    SIMACTION UB_CONF UB_CONF2 SIMILAR e e1 SIMCONFIG
    UB_IMPL UB_CS H.
  generalize dependent addrs.
  generalize dependent lfs.
  generalize dependent lfs0.
  induction H0...
  destruct addrs; isa; [ contradiction | discriminate ].
  destruct addrs; try discriminate...
  destruct lfs; try discriminate...
  destruct (eq_nat_dec a x); subst.
  unfold alloc in ONHEAP2; unfold Common.alloc in ONHEAP1...
  unfold set in ONHEAP2; unfold Common.set in ONHEAP1...
  destruct eq_nat_dec; try tauto...
  inversion HEAD; subst.
  inversion ONHEAP2; subst.
  inversion ONHEAP1; subst.
  exists lf_fla...
  inversion ONHEAP1; subst; discriminate.
  destruct IN as [ | IN ]; try tauto.
  unfold alloc in ONHEAP2; unfold Common.alloc in ONHEAP1...
  unfold set in ONHEAP2; unfold Common.set in ONHEAP1...
  destruct (eq_nat_dec x a); subst; try tauto...
  destruct lfs0; inversion RLFS; subst.
  apply IHSimilar_clos with (lfs0 := lfs0) (lfs := lfs)
    (addrs := addrs)...
  rewrite (Common.alloc_nin _ Gamma addrs) in ONHEAP1...
  rewrite (alloc_nin SGamma addrs) in ONHEAP2...
  inversion SIMHEAP; subst; eauto.
exists Val; split...
econstructor; eauto.
rewrite LENGTH.
erewrite rebuild_lfs_length; eauto...
inversion SIMHEAP; subst...
apply -> DOM...
(* Case_of_Eval *)
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMCONFIG; subst.
inversion SIMEXPR; subst.
remember (E
  (Config SGamma e1 sigma (args, length args) pclo),
  K_alt p_als fake_bot :: K0) as Conf.
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
  inversion UB_CONF; subst.
  inversion UBEXPR...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
  constructor...
  eapply Stack_sim_alt...
  apply FINDALS.
  auto.
exists Val; split...
(* Case_of_Apply *)
rename Delta into Gamma.
inversion SIMILAR; subst.
inversion SIMACTION; subst.
inversion SIMVALUE; subst.
inversion SIMSTACK  as [ | | K1 SS1 p_alts0 alts0 ]; subst.
destruct (sim_select_case C cs _ _ _ _ HS SELECT)
  as [Xp_e [Xe [Xnth [Xfind Xreb]]]].
remember (E (Config SGamma Xe (addrs ++ theta) (args0, fake_bot) pclo), SS1)
  as Conf...
assert (UB_CONF2 : UB_conf stat Conf).
  subst; constructor.
  inversion UB_CS; subst.
  assert (UBNODE := UBIN _ _ Xfind).
  inversion UBNODE; subst...
destruct (IHDEVAL Conf UB_CONF2) as [Val [RED SIM]]; subst...
exists Val; split...
econstructor; eauto.
Qed.

Lemma Reb_to_Reblfs :
forall cs l e_fla lfs e
  (REB : Rebuild cs (Letrec l e_fla) (CU.Letrec lfs e)),
  Rebuild_lfs cs l lfs.
Proof with isa.
intros.
inversion REB...
Qed.

Lemma length_lfs_not_eq :
forall cs lfs_fla lfs
  (LENNEQ : length lfs_fla <> length lfs),
  ~ Rebuild_lfs cs lfs_fla lfs.
Proof.
intros.
intro H.
induction H; subst; simpl in *; auto.
Qed.

Lemma length_als_not_eq :
forall cs als_fla als
  (LENNEQ : length als_fla <> length als),
  ~ Rebuild_alts cs als_fla als.
Proof.
intros.
intro H.
induction H; subst; simpl in *; auto.
Qed.

Ltac destr_discr X := destruct X; [ |
  let NOTREB := fresh "NOTREB" in right; intro NOTREB;
  inversion NOTREB; subst; intuition ].

Ltac n := try (right; intro H; inversion H).

Definition verify : forall (e : D.expr) (cs : code_store)
  (e_fla : expr), {Rebuild cs e_fla e} + {~ Rebuild cs e_fla e}.
Proof with isa.
intro.
induction e using CU.expr_rec2...
(* App *)
destruct e_fla; [ | n | n | n ].
destr_discr (var_eq_dec v x).
destr_discr (vars_eq_dec v0 xs).
destr_discr (eq_nat_dec c cu); subst.
left; constructor.
(* Cons *)
destruct e_fla; [ n | | n | n ].
destr_discr (eq_nat_dec c C).
destr_discr (vars_eq_dec v xs).
destr_discr (eq_nat_dec c0 cu); subst.
left; constructor.
(* Letrec *)
destruct e_fla; [ n | n | | n ].
destr_discr (IHe cs e_fla).
destruct (eq_nat_dec (length l) (length lfs)); [ |
  right; intro H; inversion H; subst;
  apply length_lfs_not_eq with (cs := cs) in n ]...
generalize dependent l.
induction lfs...
  (* nil *)
destruct l; try discriminate...
left; constructor...
constructor.
  (* cons *)
destruct l; try discriminate...
assert (LFa := LF a (or_introl _ (refl_equal _))).
destruct a.
destruct p.
assert (LFlfs : forall lf : gen_lambda_form,
  In lf lfs -> match lf with
  | Lf _ _ _ f =>
      forall (cs : code_store) (e_fla : expr),
      {Rebuild cs e_fla f} + {~ Rebuild cs e_fla f}
  end)...
  apply LF; right...
inversion e0.
assert (IH := IHlfs LFlfs l H0).
destruct IH; [ |
  let H := fresh "H" in
  (right; intro H; inversion H; subst; inversion RLFS;
  subst; assert (Rebuild cs (Letrec l e_fla) (CU.Letrec lfs e));
  [constructor; auto | contradiction]) ].
apply Reb_to_Reblfs in r0.
destr_discr (vars_eq_dec v v0); [ subst | inversion RLFS; subst; tauto ].
case_eq (find_cs cs c); intros; try let HH := fresh "H" in
  right; intro HH; inversion HH; subst; inversion RLFS; subst;
  rewrite H in *; discriminate.
destruct l0.
assert (LFe2 := LFa cs e2).
destruct LFe2;
  [ | let HH := fresh "H" in right; intro HH; inversion HH;
  subst; inversion RLFS; subst; rewrite H in *; inversion FIND;
  subst; tauto ].
destruct (upd_flag_eq_dec u0 u); 
  [ | let HH := fresh "H" in right; intro HH; inversion HH;
  subst; inversion RLFS; subst; rewrite H in *; inversion FIND;
  subst; tauto ].
destruct (vars_eq_dec v0 v);
  [ | let HH := fresh "H" in right; intro HH; inversion HH;
  subst; inversion RLFS; subst; rewrite H in *; inversion FIND;
  subst; tauto ].
destruct (eq_nat_dec b0 b);
  [ | let HH := fresh "H" in right; intro HH; inversion HH;
  subst; inversion RLFS; subst; rewrite H in *; inversion FIND;
  subst; tauto ]; subst.
left; constructor...
apply Reblf_cons with (f := e2)...
(* Case *)
destruct e_fla; [ n | n | n | ].
case_eq (find_cs cs c); intros;
 try let HH := fresh "H" in
  right; intro HH; inversion HH; subst; inversion RALS; subst;
  rewrite H in *; discriminate.
destr_discr (IHe cs e_fla).
rename a into als_fla.
assert (REBALS : {Rebuild_alts cs als_fla als} +
    {~ Rebuild_alts cs als_fla als}).
  clear IHe H.
  destruct (eq_nat_dec (length als_fla) (length als)) as [ e0 | NEQ ];
  [ | let HH := fresh "H" in
    right; intro HH; inversion HH; subst; simpl in *; auto;
    assert (NEQ2 : length als0 <> length Dals); auto;
    apply length_als_not_eq with (cs := cs) in NEQ2; tauto ].
  generalize dependent als_fla.
  induction als...
  (* nil *)
  left; induction als_fla; simpl in *; try discriminate.
  constructor.
  (* cons *)
  destruct als_fla; try discriminate...
  assert (ALSa := ALS a (or_introl _ (refl_equal _))).
  destruct a.
  destruct a0.
  assert (ALSals : forall al : gen_alt,
    In al als -> match al with
    | Alt _ f =>
        forall (cs : code_store) (e_fla : expr), 
        {Rebuild cs e_fla f} + {~ Rebuild cs e_fla f}
    end)...
    apply ALS; right...
  case_eq (find_cs cs c0); intros; try let HH := fresh "H" in
    right; intro HH; inversion HH; subst; rewrite H in *; discriminate.
  assert (ALSace := ALSa cs e2).
  destruct ALSace; [ | try let HH := fresh "H" in
    right; intro HH; inversion HH; subst;
    rewrite H in *; inversion FIND; subst; tauto ].
  inversion e0 as [ LEN ].
  assert (REBTAIL := IHals ALSals als_fla LEN).
  destr_discr REBTAIL.
  destr_discr (eq_nat_dec b b0); subst; left.
  apply Rebal_cons with (e := e2)...
destruct REBALS; [ | let HH := fresh "H" in
  right; intro HH; inversion HH; subst;
  rewrite H in *; inversion FINDALS; subst; tauto ].
left; apply Reb_Case with (als := als_fla)...
Qed.

Definition compile (d_e : D.expr) : option
  { x : code_store * expr * statistics
  | match x with
    (cs, e, stat) =>
      UB stat e /\
      UB_cs stat cs /\
      Implements cs stat /\
      Rebuild cs e d_e        
    end }.
Proof with isa; auto with arith.
intro.
refine ( match flatten 0 d_e with (_, cs, e) => _ end ).
destruct (gather_stats e) as [[stats_e_app stats_e_cons] UB_e].
destruct (gather_stats_cs cs) as [[stats_cs_app stats_cs_cons] UBCS_cs].
remember (max stats_e_app stats_cs_app,
          set_union cons_times_nat_eq_dec stats_e_cons stats_cs_cons)
  as stats_final.
destruct stats_final as [stats_final_app stats_final_cons].
remember
  (impl_for_pap stats_final_app ++ impl_for_cons stats_final_cons ++ cs)
  as cs_final .
destruct (verify d_e cs_final e); [ | exact None ].
refine (Some _).
exists (cs_final, e, (stats_final_app, stats_final_cons)).
inversion Heqstats_final; subst.
split.
(* UB *)
apply UB_weaken with (spap := stats_e_app) (scons := stats_e_cons)...
split.
(* UB_cs *)
apply impl_for_UB.
apply UB_cs_weaken with (spap := stats_cs_app) (scons := stats_cs_cons)...
split.
(* Implements *)
apply impl_for_implement.
(* Rebuild *)
apply r.
Qed.
