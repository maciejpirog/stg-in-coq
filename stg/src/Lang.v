(** STG in COQ by Maciej Piróg, University of Wrocław, 2010 *)

(** This library contains definitions of expressions, basic properities
and operations. *)

Require Export Arith.
Require Export FunctionalExtensionality.
Require Export List.
Require Export Utils.

(** * Language definition *)

(** Note on binders:

There are three kinds of binders:
- [Letrec] binds the defined subexpressions
- [Lf] (lambda-form) binds its arguments (that is, in the lambda form
  [\(pi)xyz.e] the [x], [y], [z] variables are bound)
- [Alt] (alternative in a case expression) binds arguments of the
  constructor.

For simplicity of this documentation we will sometimes use a simplified
quasi-language, where [bind[n]] is a binder which binds [n] variables.

Most of functions and predicates operating on (sub)expressions have the
[offset] argument, which indicates the number of binders in the
super expression on the path from the top node to the subexpression.
For example, the [n]-th variable (ie. [Index n]) in the expression
[bind[3].bind[2].e], is the ([n+3])-th variable in the expression
[bind[2].e], and the ([n+5])-th variable in the expression [e].
The offset indicates the "+x" value. For example, the quasi-function
for counting the number of occurences of the [n]-th variable may look
like:
[[

Fixpoint number_of_occ (offset : nat) (n : nat) (expr : e) {struct e}
  : nat :=
match e with
| Pair e1 e2 => number_of_occ offset n e1 + number_of_occ offset n e2
| Index m => if eq_nat_dec m (n + offset) then 1 else 0 
| bind[k].e => number_of_occ (offset + k) n e
end
]]

In the example we could just skip the [offset] argument and add [k] to
[n] in the third alternative, but in the general case it is insufficient,
like in the [map_expr : forall (op : var -> var) (offset : nat),
expr -> expr] function, where [op] is arbitrary.
*)

Definition atom := nat.

Inductive var : Set :=
| Index : nat -> var
| Atom : atom -> var.

Definition eq_var_dec : forall (v v0 : var), {v = v0} + {v <> v0}.
intros.
repeat decide equality.
Defined.

Definition is_atom (v : var) : Prop :=
match v with
| Index _ => False
| Atom _ => True
end.

Definition vars := list var.

Definition are_atoms (vs : vars) :=
forall (a : var), In a vs -> is_atom a.

Definition constructor := nat.

Definition bind := nat.

Inductive upd_flag : Set :=
| Update : upd_flag
| Dont_update : upd_flag.

Inductive expr : Set :=
| App : var -> vars -> expr
| Constr : constructor -> vars -> expr
| Letrec : list lambda_form -> expr -> expr
| Case : expr -> list alt -> expr
with lambda_form : Set :=
| Lf : upd_flag -> bind -> expr -> lambda_form
with alt : Set :=
| Alt : constructor -> bind -> expr -> alt.

Definition defs := list lambda_form.

Definition alts := list alt.

Theorem expr_ind2 :
forall (P0 : expr -> Prop)
  (P1 : lambda_form -> Prop)
  (P2 : alt -> Prop),
(forall (v : var) (vs : vars), P0 (App v vs)) ->
(forall (c : constructor) (vs : vars), P0 (Constr c vs)) ->
(forall (ds : defs) (e : expr), P0 e ->
  (forall d, In d ds -> P1 d) -> P0 (Letrec ds e)) ->
(forall (e : expr) (als : alts), P0 e ->
  (forall a, In a als -> P2 a) -> P0 (Case e als)) ->
(forall (pi : upd_flag) (b : bind) (e : expr), P0 e -> P1 (Lf pi b e)) ->
(forall (c : constructor) (b : bind) (e : expr), P0 e ->
  P2 (Alt c b e)) ->
forall e : expr, P0 e.
Proof.
intros P0 P1 P2.
intros app cons letr case lf al.
refine (fix IH0 (e : expr) : P0 e := _
        with IH1 (lf0 : lambda_form) : P1 lf0 := _
        with IH2 (al0 : alt) : P2 al0 := _
        for IH0).
case e; intros.
(* App *)
apply app.
(* Constr *)
apply cons.
(* Letrec *)
apply letr.
apply IH0.
induction l.
intros; simpl in *; contradiction.
intros; simpl in *; destruct H.
rewrite <- H.
apply IH1.
apply IHl.
apply H.
(* Case *)
apply case.
apply IH0.
induction l.
intros; simpl in *; contradiction.
intros; simpl in *; destruct H.
rewrite <- H.
apply IH2.
apply IHl.
apply H.
(* Lf *)
destruct lf0.
apply lf.
apply IH0.
(* Alt *)
destruct al0.
apply al.
apply IH0.
Qed.

(** * Structural integrity of expressions *)

(** The [closed_by_expr] predicate holds if each variable in the term
either:
- is an atom
- is an index, but does not exceed [limit]
- is present in the [ms] set.

Limit is also an offset for variables in [ms], for example:
[( closed_by_expr [3] 2 (bind[5] (Index 10)) )] holds, but
[( closed_by_expr [3] 2 (bind[5] (Index 7)) )] does not.
 *)

Inductive closed_by_var (ms : list nat) (limit : nat) : var -> Prop :=
| closed_by_var_env : forall (m : nat), In m ms ->
  closed_by_var ms limit (Index (m + limit))
| closed_by_var_index : forall (m : nat), m < limit ->
  closed_by_var ms limit (Index m)
| closed_by_var_atom : forall (a : atom), closed_by_var ms limit (Atom a).

Inductive closed_by_vars (ms : list nat) (limit : nat) (vs : vars) :
  Prop :=
| closed_by_vars_c : (forall v, In v vs -> closed_by_var ms limit v) ->
  closed_by_vars ms limit vs.

Inductive closed_by_expr (ms : list nat) (limit : nat) : expr -> Prop :=
| closed_by_app : forall v vs,
  closed_by_var ms limit v ->
  closed_by_vars ms limit vs ->
  closed_by_expr ms limit (App v vs)
| closed_by_constr : forall c vs,
  closed_by_vars ms limit vs ->
  closed_by_expr ms limit (Constr c vs)
| closed_by_letrec : forall ds e,
  (forall lf, In lf ds -> closed_by_lf ms (limit + length ds) lf) ->
  closed_by_expr ms (limit + length ds) e ->
  closed_by_expr ms limit (Letrec ds e)
| closed_by_case : forall e als,
  closed_by_expr ms limit e ->
  (forall al, In al als -> closed_by_alt ms limit al) ->
  closed_by_expr ms limit (Case e als)
with closed_by_lf (ms : list nat) (limit : nat) : lambda_form -> Prop :=
| closed_by_lf_c : forall pi b e,
  closed_by_expr ms (limit + b) e ->
  closed_by_lf ms limit (Lf pi b e)
with closed_by_alt (ms : list nat) (limit : nat) : alt -> Prop :=
| closed_by_c : forall c b e,
  closed_by_expr ms (limit + b) e ->
  closed_by_alt ms limit (Alt c b e).

Definition closed_expr (limit : nat) (e : expr) : Prop :=
closed_by_expr nil limit e.

Definition closed_lf (limit : nat) (lf : lambda_form) : Prop :=
closed_by_lf nil limit lf.

Definition closed_alt (limit : nat) (al : alt) : Prop :=
closed_by_alt nil limit al.

(** Not-bound vars are those indices which exceeds the number of 
binders on the path from the top node of the term. Atoms are NOT
not-bound. *)

Definition not_bound_var (offset : nat) (v : var) : option nat :=
match v with
| Atom _ => None
| Index n => if le_lt_dec offset n then Some (n - offset) else None
end.

(** To define the set of not bound vars of an expression, we need to
sum up some sets represented as lists. (For no reason) we do not
use Coq std library notion of finite sets, so we encode the addition of
sets of sets by [flat_map]. Since Coq does not like [flat_map] in
recursion, we use a composition of [flat] (defined below) and [map],
which is ok for recursion. *)

Fixpoint flat (A : Type) (l : list (list A)) {struct l} : list A :=
match l with
| nil => nil
| x :: xs => x ++ flat A xs
end.

Implicit Arguments flat [A].

Lemma flat_map_flat_map :
forall (A B : Type) (f : A -> list B) (xs : list A),
  flat (map f xs) = flat_map f xs.
Proof with isa.
induction xs...
f_equal...
Qed.

Lemma map_flat_map :
forall (A B : Type) (f : A -> B) (xss : list (list A)),
  map f (flat xss) = flat (map (map f) xss).
Proof with isa.
induction xss...
rewrite map_app...
f_equal...
Qed.

Definition not_bound_vars (offset : nat) (vs : vars) : list nat :=
fold_right (fun v ns =>
  match not_bound_var offset v with
  | Some k => k :: ns
  | None => ns
  end) nil vs.

Fixpoint not_bound_expr (offset : nat) (e : expr) 
  {struct e} : list nat :=
match e with
| App v vs => not_bound_vars offset (v :: nil) ++
    not_bound_vars offset vs
| Constr c vs => not_bound_vars offset vs
| Letrec ds f => flat (map (not_bound_lf (offset + length ds)) ds) ++
    not_bound_expr (offset + length ds) f
| Case f als => flat (map (not_bound_alt offset) als) ++
    not_bound_expr offset f
end
with not_bound_lf (offset : nat) (lf : lambda_form)
  {struct lf} : list nat :=
match lf with
| Lf pi b e => not_bound_expr (offset + b) e
end
with not_bound_alt (offset : nat) (al : alt) {struct al} : list nat :=
match al with
| Alt c b e => not_bound_expr (offset + b) e
end.

(** Note that the [fv] function gathers those indices which
are not bound. Atoms are not regarded free variables, because
the [fv] function is used in those semantics where [no_atoms] invariant
is meant to hold on all terms. *)

Definition fv x := map Index (not_bound_lf 0 x).

(** * Maps and functional composition *)

(** Addition and subtraction of indices in variables *)

Definition plus_offset (offset : nat) (v : var) : var :=
match v with
| Index n => Index (n + offset)
| Atom a => Atom a
end.

Definition minus_offset (offset : nat) (v : var) : var :=
match v with
| Index n => Index (n - offset)
| Atom a => Atom a
end.

Theorem plusminus_offset_invariant :
forall (v : var) (o : nat), minus_offset o (plus_offset o v) = v.
Proof.
induction v; intros; simpl.
f_equal; omega.
auto.
Qed.

(** The [apply_with_offset] function applies [op] to a variable in 
an offset-sensitive way. For example, consider [op] defined as:
[[

Definition f (v : var) : var :=
match v with
| Index 5 => Index 105
| _ => v
end
]]
then:
[[

apply_with_offset f 2 (Index 8) = Index 8 
apply_with_offset f 2 (Index 7) = Index 107
]]
The function is an identity on indices lower than the offset.
*)

Definition apply_with_offset (op : var -> var) (offset : nat) (v : var)
  : var :=
match v with
| Index n => if le_lt_dec offset n
    then plus_offset offset (op (minus_offset offset v))
    else v
| Atom a => plus_offset offset (op v)
end.

(** The [map_expr] function applies the [apply_with_offset] function
to all variables in the term. *)

Fixpoint map_expr (op : var -> var) (offset : nat) (e : expr) 
  {struct e} : expr :=
match e with
| App v vs => App
    (apply_with_offset op offset v)
    (map (apply_with_offset op offset) vs)
| Constr c vs => Constr c
    (map (apply_with_offset op offset) vs)
| Letrec ds f => Letrec
    (map (map_lf op (offset + length ds)) ds)
    (map_expr op (offset + length ds) f)
| Case f als => Case 
    (map_expr op offset f)
    (map (map_alt op offset) als)
end
with map_lf (op : var -> var) (offset : nat) (lf : lambda_form) 
  {struct lf} : lambda_form :=
match lf with
| Lf pi b e => Lf pi b (map_expr op (offset + b) e)
end
with map_alt (op : var -> var) (offset : nat) (al : alt) 
  {struct al} : alt :=
match al with
| Alt c b e => Alt c b (map_expr op (offset + b) e)
end.

(** Obviously, applying [f] with offset [0] is equal to [f], and its
eta-expanded version *)

Lemma apply_with_offset_0_id :
forall (f : var -> var), apply_with_offset f 0 = f.
Proof with isa.
isa.
unfold apply_with_offset.
apply functional_extensionality...
destruct x; unfold plus_offset...
try rewrite arith_m_minus_O_EQ_m; destruct f...
destruct f...
Qed.

Lemma apply_with_offset_0_v :
forall (f : var -> var) (v : var), apply_with_offset f 0 v = f v.
Proof.
isa.
rewrite apply_with_offset_0_id.
isa.
Qed.

(** The [map_expr] function is composable on a fixed offset, that is:

[map_expr f n (map_expr g n e) = map_expr (compose f g) n e]
*)

Definition compose (A B C : Set) (f : B -> C) (g : A -> B) : A -> C :=
fun x : A => f (g x).

Implicit Arguments compose [A B C]. 

Definition composable (S : Set) (gmap : (var -> var) -> nat -> S -> S)
  : S -> Prop :=
fun x : S => forall (f g : var -> var) (o : nat),
  compose (gmap f o) (gmap g o) x = gmap (compose f g) o x.

Implicit Arguments composable [S].

Theorem apply_with_offset_composable :
forall (v : var) (f g : var -> var) (o : nat),
  apply_with_offset f o (apply_with_offset g o v) =
  apply_with_offset (fun x : var => f (g x)) o v.
Proof with isa.
intros.
unfold apply_with_offset.
case v...
destruct le_lt_dec;
  try (rewrite plusminus_offset_invariant; simpl; case g; isa);
  case (le_lt_dec); isa;
  assert (H : o <> o); try omega; destruct H; auto.
rewrite plusminus_offset_invariant; simpl.
case g...
case (le_lt_dec); isa;
  assert (H : o <> o); try omega; destruct H; auto.
Qed.

Hint Resolve apply_with_offset_composable.

Theorem map_expr_composable :
forall e : expr, composable map_expr e.
Proof with isa.
intros.
induction e using expr_ind2 with
  (P1 := composable map_lf)
  (P2 := composable map_alt);
  unfold composable; unfold compose; simpl; intros; f_equal;
  try rewrite map_length; try apply IHe; isa.
(* App *)
induction vs; isa; f_equal...
(* Constr *)
induction vs; isa; f_equal...
(* Letrec *)
generalize o; clear o.
induction ds...
f_equal; try (repeat rewrite arith_a_plus_Sb_EQ_Sa_plus_b; apply IHds;
    intros);
  apply H; intuition.
(* Case *)
induction als; isa; f_equal; try (apply IHals; intros); apply H; intuition.
Qed.

Theorem map_expr_compose :
forall (f g : var -> var) (e : expr) (n : nat),
  map_expr f n (map_expr g n e) = map_expr (compose f g) n e.
Proof.
intros.
apply map_expr_composable.
Qed.

(** * Values (normal forms) *)

(** Obviously, not all applications are values, it depends on
the definition of the heap node represented by the variable in
the head of the application. The following definition may be thus
regarded as an internal, for purpose of proofs. *)

Inductive is_value : expr -> Prop :=
| value_var : forall p ps, is_value (App p ps)
| value_constr : forall c ps, is_value (Constr c ps).

Hint Constructors is_value.

(** * More on atoms *)

Lemma atoms_closed_constr :
forall c ps, closed_expr 0 (Constr c ps) -> are_atoms ps.
Proof with intuition.
intros.
inversion H; subst.
inversion H1.
unfold are_atoms.
intros.
case H0 with (v := a)...
inversion H3.
unfold is_atom...
Qed.

Lemma atoms_app :
forall ps qs, are_atoms ps -> are_atoms qs -> are_atoms (ps ++ qs).
Proof.
intros.
unfold are_atoms in *.
isa.
apply in_app_or in H1.
intuition.
Qed.

Lemma atoms_app2 :
forall ps qs, are_atoms (ps ++ qs) -> are_atoms ps /\ are_atoms qs.
Proof.
intros.
unfold are_atoms in *.
split; isa; apply H; apply in_or_app; isa.
Qed.

Lemma atoms_head :
forall (p : var) (ps : vars), are_atoms (p :: ps) -> is_atom p.
Proof.
intuition.
Qed.

Lemma atoms_tail :
forall (p : var) (ps : vars), are_atoms (p :: ps) -> are_atoms ps.
Proof.
intros.
unfold are_atoms in *.
isa.
Qed.

Lemma atoms_cons :
forall (p : var) (ps : vars), are_atoms (p :: ps) ->
  are_atoms ps /\ is_atom p.
Proof with auto.
isa.
split.
apply atoms_tail with (p := p)...
apply atoms_head with (ps := ps)...
Qed.

Lemma atoms_firstn :
forall ats n, are_atoms ats -> are_atoms (firstn n ats).
Proof.
intros.
unfold are_atoms in *.
intros.
apply In_firstn in H0. 
apply H; auto.
Qed.

Lemma atoms_nil :
are_atoms nil.
Proof.
unfold are_atoms.
intros.
inversion H.
Qed.

Lemma atoms_map_atom :
forall (ats : list atom), are_atoms (map Atom ats).
Proof.
isa.
unfold are_atoms.
isa.
apply in_map_iff in H.
destruct H.
destruct H.
subst.
unfold is_atom.
trivial.
Qed.

(** The [to_atom] tactic transforms a selected variable into an atom
whenever the [is_atom] predicate is present in the assumptions:
[[
a : var, H : is_atom a, _ |- _
Coq < to_atom a
a : atom, H : is_atom (Atom a), _ |- _
]] *)

Ltac to_atom a := destruct a; [ isa; contradiction | ].

Lemma atoms_exists :
forall (vs : vars), are_atoms vs ->
  exists ats : (list atom), vs = map Atom ats.
Proof with isa.
intros.
induction vs...
exists nil.
simpl...
apply atoms_cons in H; destruct H.
apply IHvs in H.
destruct H.
destruct a; try contradiction.
exists (a :: x).
simpl.
f_equal...
Qed.

Lemma atoms_map_injection :
forall vs ws, map Atom vs = map Atom ws -> vs = ws.
Proof with isa.
intro.
induction vs...
induction ws...
discriminate H.
induction ws...
discriminate H.
f_equal.
injection H.
intuition.
apply IHvs.
injection H.
intuition.
Qed.

Lemma atoms_skipn :
forall ats n,
  are_atoms ats ->
  are_atoms (skipn n ats).
Proof with isa.
intros.
unfold are_atoms in *.
intros.
apply H.
apply In_skipn with (n := n)...
Qed.

Lemma atom_in_map_atom :
forall a ats,
  In a (map Atom ats) ->
  is_atom a.
Proof with isa.
induction ats...
contradiction.
destruct H...
subst...
Qed.

(** * [no_atoms] restriction *)

(** From the Explicit Environment Semantics forward we make a clear
distinction between variables in expressions and addresses on the heap.
Therfore no [Atom] variable can occur in any expression. The obvious
way to guarantee that would be to declare another datatype
inhabited by such atom-free expressions along with a (rather trivial)
conversion function. But we want to stick to only one language, so we
define the [no_atoms] predicate which is an invariant for all expressions
used in semantics that use environments and do not make substitutions on
expressions. *)

Inductive no_atoms_var : var -> Prop :=
| no_atom_var_c : forall (n : nat), no_atoms_var (Index n).

Inductive no_atoms_vars (vs : vars) : Prop :=
| no_atoms_vars_c : (forall v, In v vs -> no_atoms_var v) ->
  no_atoms_vars vs.

Inductive no_atoms : expr -> Prop :=
| no_atoms_app : forall v vs,
  no_atoms_var v ->
  no_atoms_vars vs ->
  no_atoms (App v vs)
| no_atoms_constr : forall c vs,
  no_atoms_vars vs ->
  no_atoms (Constr c vs)
| no_atoms_letrec : forall ds e,
  (forall lf, In lf ds -> no_atoms_lf lf) ->
  no_atoms e ->
  no_atoms (Letrec ds e)
| no_atoms_case : forall e als,
  no_atoms e ->
  (forall al, In al als -> no_atoms_alt al) ->
  no_atoms (Case e als)
with no_atoms_lf : lambda_form -> Prop :=
| no_atoms_lf_c : forall pi b e,
  no_atoms e ->
  no_atoms_lf (Lf pi b e)
with no_atoms_alt : alt -> Prop :=
| no_atoms_alt_c : forall c b e,
  no_atoms e ->
  no_atoms_alt (Alt c b e).

Hint Constructors no_atoms.
