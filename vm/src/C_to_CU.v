Require Import List.
Require Import Arith.
Require Import FunctionalExtensionality.

(** * Compiling C to CU *)

Require Import C.
Require Import CU.

Fixpoint compute_cleanup_n (n : nat) (e : C.expr) {struct e} : CU.expr :=
match e with
| C.App x xs => CU.App x xs (n)
| C.Constr C xs => CU.Constr C xs (n)
| C.Letrec lfs f => CU.Letrec
    (map (fun lf => match lf with
       Lf pi xs bind e => Lf pi xs bind (compute_cleanup_n bind e)
    end) lfs)
    (compute_cleanup_n (length lfs + n) f)
| C.Case f als => CU.Case (compute_cleanup_n 0 f)
    (map (fun alt => match alt with
       Alt bind e => Alt bind (compute_cleanup_n (bind + n) e)
    end) als)
end.

Definition compile : C.expr -> CU.expr := compute_cleanup_n 0.

(* Completeness *)

Hint Constructors C.Sem CU.Sem.

Definition clo_cleanup (clo : C.closure) :=
match clo with
| (Node (Lf pi xs bind e), vs) =>
    (Lf pi xs bind (compute_cleanup_n bind e) : node, vs)
| (Bloack_hole, addrs) => (Black_hole, addrs)
end.

Definition promote_heap (g : C.heap) : CU.heap :=
(heap_map clo_cleanup g).

Definition promote_value (v : C.value) : CU.value :=
match v with
| C.Val_con Gamma C ps => CU.Val_con (promote_heap Gamma) C ps
| C.Val_pap Gamma p ps => CU.Val_pap (promote_heap Gamma) p ps
end.

Create HintDb c_cu.

Theorem promote_on_heap :
forall Gamma p pi clovars bind e some_clo
  (ONHEAP : Gamma p = Some (Lf pi clovars bind e : node, some_clo)),
  promote_heap Gamma p =
    Some (Lf pi clovars bind (compute_cleanup_n bind e) : node, some_clo).
Proof with isa.
intros.
unfold promote_heap; unfold heap_map.
rewrite ONHEAP...
Qed.

Lemma look_up_app :
forall sigma clo x p tau
  (LOOKUP : look_up sigma clo x = Some p),
  look_up (sigma ++ tau) clo x = Some p.
Proof with isa.
intros.
unfold look_up in *.
destruct x...
revert n LOOKUP.
induction sigma; isa; destruct n; try discriminate...
Qed.

Lemma map_env_app :
forall xs addrs sigma tau clo
  (MAPENV : map_env sigma clo xs = Some addrs),
  map_env (sigma ++ tau) clo xs = Some addrs.
Proof with isa.
induction xs...
rename a into x.
remember (map_env sigma clo xs) as ME.
destruct ME as [addrs0 | ?]; try discriminate.
remember (look_up sigma clo x) as LU.
destruct LU as [addr0 | ?]; try discriminate.
rewrite <- MAPENV.
symmetry in HeqME; apply IHxs with (tau := tau) in HeqME; rewrite HeqME.
symmetry in HeqLU; apply look_up_app with (tau := tau) in HeqLU;
  rewrite HeqLU...
Qed.

Lemma make_closure_app :
forall sigma tau current_clo lf closure
  (CLOS : make_closure (Expr := C.expr) sigma current_clo lf =
    Some closure),
  make_closure (sigma++tau) current_clo lf = Some closure.
Proof with isa.
intros.
unfold make_closure in *.
destruct lf.
remember (map_env sigma current_clo v) as ME.
destruct ME as [addrs | ?]; try discriminate.
symmetry in HeqME; apply map_env_app with (tau := tau) in HeqME.
rewrite HeqME...
Qed.

Lemma make_closures_app :
forall sigma tau current_clo lfs closures
  (CLOS : make_closures (Expr := C.expr) sigma current_clo lfs =
    Some closures),
  make_closures (sigma++tau) current_clo lfs = Some closures.
Proof with isa.
induction lfs...
rename a into lf.
remember (make_closures sigma current_clo lfs) as MCS.
destruct MCS as [clos | ?]; try discriminate.
remember (make_closure sigma current_clo lf) as MC.
destruct MC as [clo | ?]; try discriminate.
rewrite <- CLOS.
rewrite IHlfs with (closures := clos)...
symmetry in HeqMC; apply make_closure_app with (tau := tau) in HeqMC;
  rewrite HeqMC...
Qed.

Lemma firstn_skipn :
forall A tau bind0 args
  (LENGTH : bind0 <= length (A := A) args),
  skipn bind0 (firstn bind0 args ++ tau) = tau.
Proof with isa; auto with arith.
induction bind0...
destruct args...
inversion LENGTH...
Qed.

Lemma skipn_add :
forall A n (sigma : list A) tau addrs,
skipn n (sigma ++ tau) =
  skipn (length addrs + n) ((addrs ++ sigma) ++ tau).
Proof with isa.
induction addrs...
Qed.

Lemma promote_set_cons :
forall Delta p C addrs,
promote_heap (set Delta p (C.make_cons C addrs)) =
  set (promote_heap Delta) p (CU.make_cons C addrs).
Proof with isa.
intros.
apply functional_extensionality...
unfold promote_heap; unfold heap_map; unfold set.
destruct (eq_nat_dec x p)...
Qed.

Lemma promote_set_pap :
forall Delta p q addrs,
set (promote_heap Delta) p (CU.make_pap q addrs) = 
  promote_heap (set Delta p (C.make_pap q addrs)).
Proof with isa.
intros.
apply functional_extensionality...
unfold promote_heap; unfold heap_map; unfold set.
destruct (eq_nat_dec x p)...
Qed.

(* Hail Coq for the following proof, which had been admitted for
such a long time that I forgot the definitions or any intuitive
understanding of the lemma. It has been proven by a random
series of unfolding and destruction late at a very dark night. *)

Lemma promote_alloc :
forall addrs Gamma closures
  (LENGTH : length addrs = length closures),
  alloc (promote_heap Gamma) addrs (map clo_cleanup closures) =
    promote_heap (alloc Gamma addrs closures).
Proof with isa.
unfold promote_heap.
induction addrs...
destruct closures...
unfold alloc in *; unfold heap_map in *...
apply functional_extensionality...
unfold set in *...
destruct eq_nat_dec...
rewrite IHaddrs in *...
Qed.

Lemma make_closures_map_cu :
forall sigma current_clo lfs closures
(CLOS : make_closures sigma current_clo lfs = Some closures),
make_closures sigma current_clo
  (map
     (fun lf : gen_lambda_form =>
      match lf with
      | Lf pi xs bind0 e0 => Lf pi xs bind0 (compute_cleanup_n bind0 e0)
      end) lfs) = Some (map clo_cleanup closures).
Proof with isa.
induction lfs; [ isa; inversion CLOS | ]...
rename a into lf.
destruct lf as [pi0 vars0 bind0 e0].
remember (make_closures sigma current_clo lfs) as MCS.
destruct MCS as [clos | ?]; try discriminate...
remember (map_env sigma current_clo vars0) as ME.
destruct ME as [addrs | ?]; try discriminate...
rewrite IHlfs with (closures := clos)...
inversion CLOS; subst.
f_equal.
Qed.

Lemma nth_map_cu :
forall C als bind0 e0 n
  (SELECT : nth C als = Some (Alt bind0 e0)),
  nth C (map
     (fun alt : gen_alt =>
      match alt with
      | Alt bind1 e1 => Alt bind1 (compute_cleanup_n (bind1 + n) e1)
      end) als) = Some (Alt bind0 (compute_cleanup_n (bind0 + n) e0)).
Proof with isa.
induction C...
destruct als.
discriminate.
destruct g; inversion SELECT; subst...
destruct als; try discriminate...
Qed.

Lemma clog_promote :
forall Gamma p,
  clog (promote_heap Gamma) p = promote_heap (clog Gamma p).
Proof with isa; eauto.
intros.
apply functional_extensionality...
unfold clog.
unfold promote_heap...
unfold heap_map.
destruct (eq_nat_dec x p)...
subst...
destruct (eq_nat_dec p p); intuition.
destruct (Gamma p)...
destruct c...
destruct n...
destruct g...
Qed.

Hint Resolve promote_on_heap map_env_app look_up_app : c_cu.

Lemma invariant :
forall Config Value
  (EVAL : C.Sem Config Value),
  match Config with
  | C.Config Gamma e sigma args clo => forall (n : nat) (tau : env),
      CU.Sem (CU.Config (promote_heap Gamma) (compute_cleanup_n n e)
             (sigma++tau) args clo)
             (promote_value Value, skipn n (sigma++tau))
  | C.Enter Gamma p ps => forall (tau : env),
      CU.Sem (CU.Enter (promote_heap Gamma) p ps tau)
             (promote_value Value, tau) 
  end.
Proof with isa; auto with c_cu.
intros.
induction EVAL...
(* Case Accum *)
eauto with c_cu.
(* Case App1 *)
apply CU.App1 with (clovars := clovars) (bind := bind)
  (some_clo := some_clo) (e := (compute_cleanup_n bind e))...
apply promote_on_heap...
(* Case App2 *)
apply CU.App2 with (clovars := clovars) (bind := bind)
  (clo := clo) (e := (compute_cleanup_n bind e))...
apply promote_on_heap...
remember (IHEVAL bind tau) as IHEVAL0; clear HeqIHEVAL0...
rewrite firstn_skipn in IHEVAL0...
(* Case App3 *)
rewrite promote_set_cons.
eapply CU.App3 with (clovars := clovars);
[ apply promote_on_heap; eauto
| rewrite clog_promote; apply IHEVAL ].
(* Case App4 *)
eapply CU.App4 with (clovars := clovars);
[ apply promote_on_heap; eauto
| rewrite clog_promote; apply IHEVAL1
| rewrite promote_set_pap; apply IHEVAL2 ].
(* Case Let *)
apply CU.Let with (addrs := addrs) (closures := map clo_cleanup closures).
rewrite LENGTH; rewrite map_length...
intros p IN;
  apply FRESH in IN;
  unfold promote_heap; unfold heap_map;
  rewrite IN...
apply make_closures_app with (tau := tau) in CLOS;
  apply make_closures_map_cu;
  rewrite <- app_ass...
assert (X := make_closures_length _ _ _ _ _ CLOS).
  assert (X0 := trans_eq LENGTH X).
  rewrite promote_alloc...
  rewrite <- app_ass.
  rewrite <- LENGTH.
  rewrite skipn_add with (addrs := addrs)...
(* Case Case_of *)
apply CU.Case_of with (bind := bind) (Delta := promote_heap Delta)
  (C := C) (addrs := addrs) (theta := sigma++tau)
  (e0 := compute_cleanup_n (bind + n) e0);
[ apply nth_map_cu
| apply IHEVAL1 with (n := 0)
| rewrite skipn_add with (addrs := addrs);
  rewrite <- app_ass; rewrite LENGTH;
  apply IHEVAL2 with (n := length addrs + n)]...
Qed.

