Require Import List.
Require Import Arith.

(** * CCP for "Current Closure Pointer" *) 

Require Import CU.
Require Import FB.

Definition expr := expr.

(* Semantics *)

Definition look_up (e : env) (g : heap) (p : address) (v : var)
  : option address :=
match v with
| B_ind n => nth n e 
| C_ind n => match g p with Some (_, clo) => nth n clo | None => None end
end.

Fixpoint map_env (e : env) (g : heap) (a : address) (vs : vars) {struct vs}
  : option addresses :=
match vs with
| nil => Some nil
| x::xs =>
  match map_env e g a xs with
  | Some ps =>
    match look_up e g a x with
    | Some p => Some (p::ps)
    | None => None
    end
  | None => None
  end
end.

Definition make_closure {Expr : Set} (e : env) (g : heap) (p : address)
  (lf : gen_lambda_form) : option (gen_closure (Expr := Expr)) :=
match lf with
| Lf _ vs _ _ =>
  match map_env e g p vs with
  | Some addrs => Some (lf : node, addrs)
  | None => None
  end
end.

Fixpoint make_closures {Expr : Set} (e : env) (g : heap) (p : address)
  (lfs : list (gen_lambda_form)) {struct lfs}
  : option (gen_closures (Expr := Expr)):=
match lfs with
| nil => Some nil
| l::lfs0 =>
  match make_closures e g p lfs0 with
  | Some clos =>
    match make_closure e g p l with
    | Some clo => Some (clo::clos)
    | None => None
    end
  | None => None
  end
end.

Inductive config : Set :=
| Config : heap -> expr -> env -> (argstack * fake_bottom)
    -> address -> config
| Enter : heap -> address -> (argstack * fake_bottom) -> env -> config.

Notation " << a , b , c , d , e >> " := (Config a b c d e) (at level 70).
Notation " << a , b , c , d >> " := (Enter a b c d) (at level 70).

Reserved Notation " a ↓ b " (at level 70, no associativity).

Inductive Sem : config -> (value * env * (argstack * fake_bottom))
  -> Prop :=

| Cons : forall Gamma C xs sigma addrs cleanup args fake_bot pclo
  (MAPENV  : map_env sigma Gamma pclo xs = Some addrs)
  (ARGSNIL : fake_bot = length args),
  << Gamma, Constr C xs (cleanup), sigma, (args, fake_bot), pclo >> ↓ (Val_con Gamma C addrs, (skipn cleanup sigma), (args, fake_bot))

| Accum : forall Gamma x xs sigma args p new_args Value cleanup fake_bot pclo
  (MAPENV  : map_env sigma Gamma pclo xs = Some new_args)
  (LOOKUP  : look_up sigma Gamma pclo x = Some p)
  (PREMISE : << Gamma, p, (new_args++args, fake_bot), skipn cleanup sigma >> ↓ Value),
  << Gamma, App x xs (cleanup), sigma, (args, fake_bot), pclo >> ↓ Value

| App1 : forall Gamma p args clovars bind e some_clo sigma fake_bot real_args fake_args
  (ONHEAP : Gamma p = Some (Lf_n clovars bind e, some_clo))
  (REAL   : real_args = firstn (length args - fake_bot) args)
  (FAKE   : fake_args = skipn (length args - fake_bot) args)
  (LENGTH : bind > length args - fake_bot),
  << Gamma, p, (args, fake_bot), sigma >> ↓ (Val_pap Gamma p real_args, sigma, (fake_args, fake_bot))

| App2 : forall Gamma p args Value e bind clo clovars sigma fake_bot
  (ONHEAP  : Gamma p = Some (Lf_n clovars bind e, clo))
  (LENGTH  : bind <= length args - fake_bot)
  (PREMISE : << Gamma, e, firstn bind args ++ sigma, (skipn bind args, fake_bot), p >> ↓ Value),
  << Gamma, p, (args, fake_bot), sigma >> ↓ Value

| App3 : forall Gamma p C addrs clovars Delta e clo sigma theta args fake_bot
  (ONHEAP  : Gamma p = Some (Lf_u clovars 0 e, clo))
  (ARGSNIL : fake_bot = length args)
  (PREMISE : << (clog Gamma p), e, sigma, (args, fake_bot), p >> ↓ (Val_con Delta C addrs, theta, (args, fake_bot))),
  << Gamma, p, (args, fake_bot), sigma >> ↓ (Val_con (set Delta p (make_cons C addrs)) C addrs, theta, (args, fake_bot))

| App4 : forall Gamma p args Value q addrs e clovars clo_e Delta sigma theta args0 fake_bot fake_bot0
  (ONHEAP1 : Gamma p = Some (Lf_u clovars 0 e, clo_e))
  (LEFT    : << (clog Gamma p), e, sigma, (args, length args), p >> ↓ (Val_pap Delta q addrs, theta, (args0, fake_bot0)))
  (RIGHT   : << set Delta p (make_pap q addrs), q, (addrs++args0, fake_bot), theta >> ↓ Value),
  << Gamma, p, (args, fake_bot), sigma >> ↓ Value

| Let : forall Gamma e lfs sigma closures Value addrs args pclo
  (LENGTH  : length addrs = length lfs)
  (FRESH   : forall p : address, In p addrs -> Gamma p = None)
  (CLOS    : make_closures (addrs++sigma) Gamma pclo lfs = Some closures)
  (PREMISE : << alloc Gamma addrs closures, e, addrs++sigma, args, pclo >> ↓ Value),
  << Gamma, Letrec lfs e, sigma, args, pclo >> ↓ Value

| Case_of : forall Gamma e als sigma pclo Value bind Delta e0 C addrs args theta args0 fake_bot fake_bot0
  (SELECT : nth C als = Some (Alt bind e0))
  (LEFT   : << Gamma, e, sigma, (args, length args), pclo >> ↓ (Val_con Delta C addrs, theta, (args0, fake_bot0)))
  (RIGHT  : << Delta, e0, addrs++theta, (args0, fake_bot), pclo >> ↓ Value),
  << Gamma, Case e als, sigma, (args, fake_bot), pclo >> ↓ Value

where " a ↓ b " := (Sem a b).
