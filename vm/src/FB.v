Require Import List.
Require Import Arith.

Require Import CU.

(** * FB for "Fake Bottom" *)

Definition heap := heap.

Definition expr := expr.

(* Semantics *)

Definition fake_bottom := nat.

Inductive config : Set :=
| Config : heap -> expr -> env -> (argstack * fake_bottom)
    -> addresses -> config
| Enter : heap -> address -> (argstack * fake_bottom) -> env -> config.

Notation " << a , b , c , d , e >> " := (Config a b c d e) (at level 70).
Notation " << a , b , c , d >> " := (Enter a b c d) (at level 70).

Reserved Notation " a ↓ b " (at level 70, no associativity).

Inductive Sem : config -> (value * env * (argstack * fake_bottom))
  -> Prop :=

| Cons : forall Gamma C xs sigma clo addrs cleanup args fake_bot
  (MAPENV  : map_env sigma clo xs = Some addrs)
  (ARGSNIL : fake_bot = length args),
  << Gamma, Constr C xs (cleanup), sigma, (args, fake_bot), clo >> ↓ (Val_con Gamma C addrs, (skipn cleanup sigma), (args, fake_bot))

| Accum : forall Gamma x xs sigma args clo p new_args Value cleanup fake_bot
  (MAPENV  : map_env sigma clo xs = Some new_args)
  (LOOKUP  : look_up sigma clo x = Some p)
  (PREMISE : << Gamma, p, (new_args++args, fake_bot), skipn cleanup sigma >> ↓ Value),
  << Gamma, App x xs (cleanup), sigma, (args, fake_bot), clo >> ↓ Value

| App1 : forall Gamma p args clovars bind e some_clo sigma fake_bot real_args fake_args
  (ONHEAP : Gamma p = Some (Lf_n clovars bind e, some_clo))
  (REAL   : real_args = firstn (length args - fake_bot) args)
  (FAKE   : fake_args = skipn (length args - fake_bot) args)
  (LENGTH : bind > length args - fake_bot),
  << Gamma, p, (args, fake_bot), sigma >> ↓ (Val_pap Gamma p real_args, sigma, (fake_args, fake_bot))

| App2 : forall Gamma p args Value e bind clo clovars sigma fake_bot
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, clo))
  (LENGTH  : bind <= length args - fake_bot)
  (PREMISE : << Gamma, e, firstn bind args ++ sigma, (skipn bind args, fake_bot), clo >> ↓ Value),
  << Gamma, p, (args, fake_bot), sigma >> ↓ Value

| App3 : forall Gamma p C addrs clovars Delta e clo sigma theta args fake_bot
  (ONHEAP  : Gamma p = Some (Lf_u clovars 0 e, clo))
  (ARGSNIL : fake_bot = length args)
  (PREMISE : << (clog Gamma p), e, sigma, (args, fake_bot), clo >> ↓ (Val_con Delta C addrs, theta, (args, fake_bot))),
  << Gamma, p, (args, fake_bot), sigma >> ↓ (Val_con (set Delta p (make_cons C addrs)) C addrs, theta, (args, fake_bot))

| App4 : forall Gamma p args Value q addrs e clovars clo_e Delta sigma theta args0 fake_bot fake_bot0
  (ONHEAP1 : Gamma p = Some (Lf_u clovars 0 e, clo_e))
  (LEFT    : << (clog Gamma p), e, sigma, (args, length args), clo_e >> ↓ (Val_pap Delta q addrs, theta, (args0, fake_bot0)))
  (RIGHT   : << set Delta p (make_pap q addrs), q, (addrs++args0, fake_bot), theta >> ↓ Value),
  << Gamma, p, (args, fake_bot), sigma >> ↓ Value

| Let : forall Gamma e lfs sigma current_clo closures Value addrs args
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) current_clo lfs = Some closures)
  (PREMISE : << alloc Gamma addrs closures, e, addrs++sigma, args, current_clo >> ↓ Value),
  << Gamma, Letrec lfs e, sigma, args, current_clo >> ↓ Value

| Case_of : forall Gamma e als sigma clo Value bind Delta e0 C addrs args theta args0 fake_bot fake_bot0
  (SELECT : nth C als = Some (Alt bind e0))
  (LEFT   : << Gamma, e, sigma, (args, length args), clo >> ↓ (Val_con Delta C addrs, theta, (args0, fake_bot0)))
  (RIGHT  : << Delta, e0, addrs++theta, (args0, fake_bot), clo >> ↓ Value),
  << Gamma, Case e als, sigma, (args, fake_bot), clo >> ↓ Value

where " a ↓ b " := (Sem a b).

