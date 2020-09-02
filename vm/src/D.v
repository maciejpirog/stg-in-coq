Require Import List.
Require Import Arith.

(** * D for "D-CPS" *)

Require Import Common.
Require Import CU.
Require Import CCP.

Definition expr := CU.expr.
Definition lambda_form := lambda_form.
Definition alt := alt.
Definition alts := list alt.

Definition heap := heap.

Definition config := CCP.config.
Definition value := (CU.value * env * (argstack * FB.fake_bottom))%type.

Inductive action : Set :=
| E : config -> action
| A : value -> action.

Inductive stack_elem : Set :=
| K_alt : alts -> FB.fake_bottom -> stack_elem
| K_upd : address -> FB.fake_bottom -> stack_elem.

Definition stack := list stack_elem.

Reserved Notation " a ^\ b " (at level 70, no associativity).

Inductive Sem : (action * stack) -> value -> Prop :=

| Halt : forall Value,
  (A Value, nil) ^\ Value

| Cons : forall Gamma C xs sigma addrs cleanup args fake_bot pclo Value K
  (MAPENV  : map_env sigma Gamma pclo xs = Some addrs)
  (ARGSNIL : fake_bot = length args)
  (PREMISE : (A (Val_con Gamma C addrs, (skipn cleanup sigma), (args, fake_bot)), K) ^\ Value),
  (E (<< Gamma, Constr C xs (cleanup), sigma, (args, fake_bot), pclo >>), K) ^\ Value

| Accum : forall Gamma x xs sigma args p new_args Value cleanup fake_bot pclo K
  (MAPENV  : map_env sigma Gamma pclo xs = Some new_args)
  (LOOKUP  : look_up sigma Gamma pclo x = Some p)
  (PREMISE : (E (<< Gamma, p, (new_args++args, fake_bot), skipn cleanup sigma >>), K) ^\ Value),
  (E (<< Gamma, App x xs (cleanup), sigma, (args, fake_bot), pclo >>), K) ^\ Value

| App1 : forall Gamma p args clovars bind e some_clo sigma fake_bot real_args fake_args Value K
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, some_clo))
  (REAL    : real_args = firstn (length args - fake_bot) args)
  (FAKE    : fake_args = skipn (length args - fake_bot) args)
  (LENGTH  : bind > length args - fake_bot)
  (PREMISE : (A (Val_pap Gamma p real_args, sigma, (fake_args, fake_bot)), K) ^\ Value),
  (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value 

| App2 : forall Gamma p args Value e bind clo clovars sigma fake_bot K
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, clo))
  (LENGTH  : bind <= length args - fake_bot)
  (PREMISE : (E (<< Gamma, e, firstn bind args ++ sigma, (skipn bind args, fake_bot), p >>), K) ^\ Value),
  (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value

| App_Eval : forall Gamma p args Value e clovars clo_e sigma fake_bot K
  (ONHEAP1 : Gamma p = Some (Lf_u clovars 0 e, clo_e))
  (PREMISE : (E (<< (clog Gamma p), e, sigma, (args, length args), p >>), K_upd p fake_bot :: K) ^\ Value),
  (E (<< Gamma, p, (args, fake_bot), sigma >>), K) ^\ Value

| App3 : forall p C addrs Delta theta args fake_bot fake_bot_dummy K Value
  (ARGSNIL : fake_bot = length args)
  (PREMISE : (A (Val_con (set Delta p (make_cons C addrs)) C addrs, theta, (args, fake_bot)), K) ^\ Value),
  (A (Val_con Delta C addrs, theta, (args, fake_bot)), K_upd p fake_bot_dummy :: K) ^\ Value

| App4 : forall p Value q addrs Delta theta args0 fake_bot fake_bot0 K
  (PREMISE : (E (<< set Delta p (make_pap q addrs), q, (addrs++args0, fake_bot), theta >>), K) ^\ Value),
  (A (Val_pap Delta q addrs, theta, (args0, fake_bot0)), K_upd p fake_bot :: K) ^\ Value

| Let : forall Gamma e lfs sigma closures Value addrs args pclo K
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) Gamma pclo lfs = Some closures)
  (PREMISE : (E (<< alloc Gamma addrs closures, e, addrs++sigma, args, pclo >>), K) ^\ Value),
  (E (<< Gamma, Letrec lfs e, sigma, args, pclo >>), K) ^\ Value

| Case_of_Eval : forall Gamma e als sigma pclo Value args fake_bot K
  (PREMISE : (E (<< Gamma, e, sigma, (args, length args), pclo >>), K_alt als fake_bot :: K) ^\ Value),
  (E (<< Gamma, Case e als, sigma, (args, fake_bot), pclo >>), K) ^\ Value

| Case_of_Apply : forall als pclo Value bind Delta e0 C addrs theta args0 fake_bot fake_bot0 K
  (SELECT  : nth C als = Some (Alt bind e0))
  (PREMISE : (E (<< Delta, e0, addrs++theta, (args0, fake_bot), pclo >>), K) ^\ Value),
  (A (Val_con Delta C addrs, theta, (args0, fake_bot0)), K_alt als fake_bot :: K) ^\ Value

where " a ^\ b " := (Sem a b).
