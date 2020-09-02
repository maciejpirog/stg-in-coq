-- correct indentation
-- deriving Prelude.Show

{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Core where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ = Prelude.error "Logical or arity value used"

false_rect :: () -> a1
false_rect _ =
  Prelude.error "absurd case"

false_rec :: () -> a1
false_rec _ =
  false_rect __

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

data Nat = O
           | S Nat

natToInt :: Nat -> Prelude.Int
natToInt O = 0
natToInt (S x) = (Prelude.+) 1 (natToInt x)

instance Prelude.Show Nat where
  show n = Prelude.show (natToInt n)

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of
    O -> f
    S n0 -> f0 n0 (nat_rect f f0 n0)

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec f f0 n =
  nat_rect f f0 n

data Option a = Some a
                | None
  deriving (Prelude.Show)

data Prod a b = Pair a b
  deriving (Prelude.Show)

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p =
  case p of
    Pair x x0 -> f x x0

prod_rec :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rec f p =
  prod_rect f p

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data Sumbool = Left
               | Right
  deriving (Prelude.Show)

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of
    Left -> f __
    Right -> f0 __

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec f f0 s =
  sumbool_rect f f0 s

data List a = Nil
              | Cons a (List a)
  deriving (Prelude.Show)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of
    Nil -> f
    Cons a l0 -> f0 a l0 (list_rect f f0 l0)

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec f f0 l =
  list_rect f f0 l

length :: (List a1) -> Nat
length l =
  case l of
    Nil -> O
    Cons a m -> S (length m)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of
    Nil -> m
    Cons a l1 -> Cons a (app l1 m)

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 l0 iHl -> case h a0 a of
                                  Left -> Left
                                  Right -> iHl) l

list_eq_dec :: (a1 -> a1 -> Sumbool) -> (List a1) -> (List a1) -> Sumbool
list_eq_dec eqA_dec l l' =
  list_rect (\l'0 -> case l'0 of
                       Nil -> Left
                       Cons y l'1 -> Right) (\x l0 iHl l'0 ->
    case l'0 of
      Nil -> Right
      Cons y l'1 ->
        (case eqA_dec x y of
           Left ->
             (case iHl l'1 of
                Left -> eq_rec_r y (eq_rec_r l'1 Left l0) x
                Right -> Right)
           Right -> Right)) l l'

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of
    Nil -> Nil
    Cons a t -> Cons (f a) (map f t)

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of
    Nil -> a0
    Cons b t -> f b (fold_right f a0 t)

type Set a = List a

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of
    Nil -> Cons a Nil
    Cons a1 x1 ->
      (case aeq_dec a a1 of
         Left -> Cons a1 x1
         Right -> Cons a1 (set_add aeq_dec a x1))

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of
    Nil -> x
    Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

eq_nat_dec :: Nat -> Nat -> Sumbool
eq_nat_dec n m =
  nat_rec (\m0 -> case m0 of
                    O -> Left
                    S m1 -> Right) (\n0 iHn m0 ->
    case m0 of
      O -> Right
      S m1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m1)) n m

max :: Nat -> Nat -> Nat
max n m =
  case n of
    O -> m
    S n' -> (case m of
               O -> n
               S m' -> S (max n' m'))

type Constructor = Nat

type Bind = Nat

data Upd_flag = Update
                | Dont_update
  deriving (Prelude.Show)

upd_flag_rect :: a1 -> a1 -> Upd_flag -> a1
upd_flag_rect f f0 u =
  case u of
    Update -> f
    Dont_update -> f0

upd_flag_rec :: a1 -> a1 -> Upd_flag -> a1
upd_flag_rec f f0 u =
  upd_flag_rect f f0 u

upd_flag_eq_dec :: Upd_flag -> Upd_flag -> Sumbool
upd_flag_eq_dec v w =
  upd_flag_rec (\w0 -> case w0 of
                         Update -> Left
                         Dont_update -> Right) (\w0 ->
    case w0 of
      Update -> Right
      Dont_update -> Left) v w

data Var = B_ind Nat
           | C_ind Nat
  deriving (Prelude.Show)

var_rect :: (Nat -> a1) -> (Nat -> a1) -> Var -> a1
var_rect f f0 v =
  case v of
    B_ind x -> f x
    C_ind x -> f0 x

var_rec :: (Nat -> a1) -> (Nat -> a1) -> Var -> a1
var_rec f f0 v =
  var_rect f f0 v

type Vars = List Var

var_eq_dec :: Var -> Var -> Sumbool
var_eq_dec v w =
  var_rec (\n w0 ->
    case w0 of
      B_ind n0 ->
        sumbool_rec (\_ -> eq_rec_r n0 Left n) (\_ -> Right)
          (nat_rec (\n1 -> case n1 of
                             O -> Left
                             S n2 -> Right) (\n1 h n2 ->
            case n2 of
              O -> Right
              S n3 ->
                sumbool_rec (\_ -> eq_rec_r n3 Left n1) (\_ -> Right) (h n3))
            n n0)
      C_ind n0 -> Right) (\n w0 ->
    case w0 of
      B_ind n0 -> Right
      C_ind n0 ->
        sumbool_rec (\_ -> eq_rec_r n0 Left n) (\_ -> Right)
          (nat_rec (\n1 -> case n1 of
                             O -> Left
                             S n2 -> Right) (\n1 h n2 ->
            case n2 of
              O -> Right
              S n3 ->
                sumbool_rec (\_ -> eq_rec_r n3 Left n1) (\_ -> Right) (h n3))
            n n0)) v w

vars_eq_dec :: Vars -> Vars -> Sumbool
vars_eq_dec vs ws =
  list_eq_dec var_eq_dec vs ws

from :: Nat -> Nat -> List Nat
from a b =
  case b of
    O -> Nil
    S m -> Cons a (from (S a) m)

data Gen_lambda_form expr = Lf Upd_flag Vars Bind expr
  deriving (Prelude.Show)

gen_lambda_form_rect :: (Upd_flag -> Vars -> Bind -> a1 -> a2) ->
                        (Gen_lambda_form a1) -> a2
gen_lambda_form_rect f g =
  case g of
    Lf x x0 x1 x2 -> f x x0 x1 x2

gen_lambda_form_rec :: (Upd_flag -> Vars -> Bind -> a1 -> a2) ->
                       (Gen_lambda_form a1) -> a2
gen_lambda_form_rec f g =
  gen_lambda_form_rect f g

data Gen_alt expr = Alt Bind expr
  deriving (Prelude.Show)

gen_alt_rect :: (Bind -> a1 -> a2) -> (Gen_alt a1) -> a2
gen_alt_rect f g =
  case g of
    Alt x x0 -> f x x0

gen_alt_rec :: (Bind -> a1 -> a2) -> (Gen_alt a1) -> a2
gen_alt_rec f g =
  gen_alt_rect f g

type Cleanup = Nat

data Expr = App Var Vars Cleanup
            | Constr Constructor Vars Cleanup
            | Letrec (List (Gen_lambda_form Expr)) Expr
            | Case Expr (List (Gen_alt Expr))
  deriving (Prelude.Show)

type Lambda_form = Gen_lambda_form Expr

type Alt0 = Gen_alt Expr

expr_eq_dec :: Expr -> Expr -> Sumbool
expr_eq_dec a b =
  case a of
    App v v0 c ->
      (case b of
         App v1 v2 c0 ->
           (case var_eq_dec v v1 of
              Left ->
                (case vars_eq_dec v0 v2 of
                   Left ->
                     (case eq_nat_dec c c0 of
                        Left ->
                          eq_rec_r c0 (eq_rec_r v2 (eq_rec_r v1 Left v) v0) c
                        Right -> Right)
                   Right -> Right)
              Right -> Right)
         _ -> Right)
    Constr c v c0 ->
      (case b of
         Constr c1 v0 c2 ->
           (case eq_nat_dec c c1 of
              Left ->
                (case vars_eq_dec v v0 of
                   Left ->
                     (case eq_nat_dec c0 c2 of
                        Left ->
                          eq_rec_r c2 (eq_rec_r v0 (eq_rec_r c1 Left c) v) c0
                        Right -> Right)
                   Right -> Right)
              Right -> Right)
         _ -> Right)
    Letrec l a0 ->
      (case b of
         Letrec l0 b0 ->
           (case eq_nat_dec (length l) (length l0) of
              Left ->
                list_rec (\l1 _ ->
                  list_rec (\_ -> expr_eq_dec a0 b0) (\a1 l2 iHl0 _ ->
                    false_rec __) l1 __) (\a1 l1 iHl l2 _ ->
                  case l2 of
                    Nil -> false_rec __
                    Cons g l3 ->
                      (case iHl l3 __ of
                         Left ->
                           (case a1 of
                              Lf u v b1 e ->
                                (case g of
                                   Lf u0 v0 b2 e0 ->
                                     (case expr_eq_dec e e0 of
                                        Left ->
                                          (case upd_flag_eq_dec u u0 of
                                             Left ->
                                               (case vars_eq_dec v v0 of
                                                  Left ->
                                                    (case eq_nat_dec b1 b2 of
                                                       Left ->
                                                         eq_rec_r b2 (\_ ->
                                                           eq_rec_r v0 (\_ ->
                                                             eq_rec_r u0
                                                               (\_ ->
                                                               eq_rec_r e0
                                                                 (\_ -> Left)
                                                                 e __) u __)
                                                             v __) b1 __
                                                       Right -> Right)
                                                  Right -> Right)
                                             Right -> Right)
                                        Right -> Right)))
                         Right -> Right)) l l0 __
              Right -> Right)
         _ -> Right)
    Case a0 l ->
      (case b of
         Case b0 l0 ->
           (case eq_nat_dec (length l) (length l0) of
              Left ->
                list_rec (\l1 _ ->
                  list_rec (\_ -> expr_eq_dec a0 b0) (\a1 l2 iHl0 _ ->
                    false_rec __) l1 __) (\a1 l1 iHl l2 _ ->
                  case l2 of
                    Nil -> false_rec __
                    Cons g l3 ->
                      (case iHl l3 __ of
                         Left ->
                           (case a1 of
                              Alt b1 e ->
                                (case g of
                                   Alt b2 e0 ->
                                     (case expr_eq_dec e e0 of
                                        Left ->
                                          (case eq_nat_dec b1 b2 of
                                             Left ->
                                               eq_rec_r b2 (\_ ->
                                                 eq_rec_r e0 (\_ -> Left) e
                                                   __) b1 __
                                             Right -> Right)
                                        Right -> Right)))
                         Right -> Right)) l l0 __
              Right -> Right)
         _ -> Right)

alt_eq_dec :: Alt0 -> Alt0 -> Sumbool
alt_eq_dec a b =
  gen_alt_rec (\b0 e b1 ->
    case b1 of
      Alt b2 e0 ->
        sumbool_rec (\_ ->
          eq_rec_r b2
            (sumbool_rec (\_ -> eq_rec_r e0 Left e) (\_ -> Right)
              (expr_eq_dec e e0)) b0) (\_ -> Right) (eq_nat_dec b0 b2)) a b

lf_eq_dec :: Lambda_form -> Lambda_form -> Sumbool
lf_eq_dec a b =
  gen_lambda_form_rec (\u v b0 e b1 ->
    case b1 of
      Lf u0 v0 b2 e0 ->
        sumbool_rec (\_ ->
          eq_rec_r u0
            (sumbool_rec (\_ ->
              eq_rec_r v0
                (sumbool_rec (\_ ->
                  eq_rec_r b2
                    (sumbool_rec (\_ -> eq_rec_r e0 Left e) (\_ -> Right)
                      (expr_eq_dec e e0)) b0) (\_ -> Right)
                  (eq_nat_dec b0 b2)) v) (\_ -> Right) (vars_eq_dec v v0)) u)
          (\_ -> Right) (upd_flag_eq_dec u u0)) a b

expr_rec2 :: (Var -> Vars -> Cleanup -> a1) -> (Constructor -> Vars ->
             Cleanup -> a1) -> (Expr -> (List (Gen_lambda_form Expr)) -> a1
             -> ((Gen_lambda_form Expr) -> () -> ()) -> a1) -> (Expr -> (List
             (Gen_alt Expr)) -> a1 -> ((Gen_alt Expr) -> () -> ()) -> a1) ->
             Expr -> a1
expr_rec2 aPP cONSTR lETREC cASE e =
  case e of
    App v v0 c -> aPP v v0 c
    Constr c v c0 -> cONSTR c v c0
    Letrec l e0 ->
      unsafeCoerce lETREC e0 l (expr_rec2 aPP cONSTR lETREC cASE e0)
        (list_rec (\lf _ -> Prelude.error "absurd case") (\a l0 iHl lf _ ->
          case in_dec lf_eq_dec lf l0 of
            Left -> iHl lf __
            Right ->
              eq_rec a
                (case a of
                   Lf u v b e1 -> expr_rec2 aPP cONSTR lETREC cASE e1) lf) l)
    Case e0 l ->
      unsafeCoerce cASE e0 l (expr_rec2 aPP cONSTR lETREC cASE e0)
        (list_rec (\al _ -> Prelude.error "absurd case") (\a l0 iHl al _ ->
          case in_dec alt_eq_dec al l0 of
            Left -> iHl al __
            Right ->
              eq_rec a
                (case a of
                   Alt b e1 -> expr_rec2 aPP cONSTR lETREC cASE e1) al) l)

type Expr0 = Expr

data Code_pointer = CP_user Nat
                    | CP_pap Nat
                    | CP_cons Constructor Nat
  deriving (Prelude.Show)

code_pointer_rect :: (Nat -> a1) -> (Nat -> a1) -> (Constructor -> Nat -> a1)
                     -> Code_pointer -> a1
code_pointer_rect f f0 f1 c =
  case c of
    CP_user x -> f x
    CP_pap x -> f0 x
    CP_cons x x0 -> f1 x x0

code_pointer_rec :: (Nat -> a1) -> (Nat -> a1) -> (Constructor -> Nat -> a1)
                    -> Code_pointer -> a1
code_pointer_rec f f0 f1 c =
  code_pointer_rect f f0 f1 c

eq_cp_dec :: Code_pointer -> Code_pointer -> Sumbool
eq_cp_dec c d =
  code_pointer_rec (\n d0 ->
    case d0 of
      CP_user n0 ->
        sumbool_rec (\_ -> eq_rec_r n0 Left n) (\_ -> Right)
          (eq_nat_dec n n0)
      _ -> Right) (\n d0 ->
    case d0 of
      CP_pap n0 ->
        sumbool_rec (\_ -> eq_rec_r n0 Left n) (\_ -> Right)
          (eq_nat_dec n n0)
      _ -> Right) (\c0 n d0 ->
    case d0 of
      CP_cons c1 n0 ->
        sumbool_rec (\_ ->
          eq_rec_r c1
            (sumbool_rec (\_ -> eq_rec_r n0 Left n) (\_ -> Right)
              (eq_nat_dec n n0)) c0) (\_ -> Right) (eq_nat_dec c0 c1)
      _ -> Right) c d

data Expr1 = App0 Var Vars Cleanup
             | Constr0 Constructor Vars Cleanup
             | Letrec0 (List (Prod Vars Code_pointer)) Expr1
             | Case0 Expr1 Code_pointer
  deriving (Prelude.Show)

expr_rect :: (Var -> Vars -> Cleanup -> a1) -> (Constructor -> Vars ->
             Cleanup -> a1) -> ((List (Prod Vars Code_pointer)) -> Expr1 ->
             a1 -> a1) -> (Expr1 -> a1 -> Code_pointer -> a1) -> Expr1 -> a1
expr_rect f f0 f1 f2 e =
  case e of
    App0 v v0 c -> f v v0 c
    Constr0 c v c0 -> f0 c v c0
    Letrec0 l e0 -> f1 l e0 (expr_rect f f0 f1 f2 e0)
    Case0 e0 c -> f2 e0 (expr_rect f f0 f1 f2 e0) c

type Lambda_form0 = Gen_lambda_form Expr1

type Alt1 = Gen_alt Code_pointer

type Alts = List Alt1

data Cs_node = CS_expr Expr1
               | CS_alts Alts
               | CS_lf Lambda_form0
               | CS_None
  deriving (Prelude.Show)

type Code_store = List (Prod Code_pointer Cs_node)

find_cs :: Code_store -> Code_pointer -> Cs_node
find_cs cs cp =
  case cs of
    Nil -> CS_None
    Cons p cs0 ->
      (case p of
         Pair cp0 node ->
           (case eq_cp_dec cp cp0 of
              Left -> node
              Right -> find_cs cs0 cp))

flatten :: Nat -> Expr0 -> Prod (Prod Nat Code_store) Expr1
flatten n e =
  case e of
    App x xs cu -> Pair (Pair n Nil) (App0 x xs cu)
    Constr c xs cu -> Pair (Pair n Nil) (Constr0 c xs cu)
    Letrec lfs e0 ->
      (case fold_right (\lf res ->
              case lf of
                Lf pi clovars bind e1 ->
                  (case res of
                     Pair y vars_ptrs ->
                       (case y of
                          Pair n1 cs1 ->
                            (case flatten n1 e1 of
                               Pair p fe2 ->
                                 (case p of
                                    Pair n2 cs2 -> Pair (Pair (S n2) (Cons
                                      (Pair (CP_user n2) (CS_lf (Lf pi
                                      clovars bind fe2)))
                                      (app cs2 (unsafeCoerce cs1)))) (Cons
                                      (Pair clovars (CP_user n2))
                                      (unsafeCoerce vars_ptrs))))))) (Pair
              (Pair n Nil) Nil) lfs of
         Pair p vars_ptrs ->
           (case p of
              Pair n3 cs3 ->
                (case flatten n3 e0 of
                   Pair p0 fe ->
                     (case p0 of
                        Pair n0 cs -> Pair (Pair n0 (app cs cs3)) (Letrec0
                          vars_ptrs fe)))))
    Case e0 als ->
      (case fold_right (\al res ->
              case al of
                Alt bind e1 ->
                  (case res of
                     Pair y als0 ->
                       (case y of
                          Pair n0 cs0 ->
                            (case flatten n0 e1 of
                               Pair p fe1 ->
                                 (case p of
                                    Pair n1 cs1 -> Pair (Pair (S n1) (Cons
                                      (Pair (CP_user n1) (CS_expr fe1))
                                      (app cs1 (unsafeCoerce cs0)))) (Cons
                                      (Alt bind (CP_user n1))
                                      (unsafeCoerce als0))))))) (Pair (Pair n
              Nil) Nil) als of
         Pair p als2 ->
           (case p of
              Pair n2 cs2 ->
                (case flatten n2 e0 of
                   Pair p0 fe ->
                     (case p0 of
                        Pair n3 cs3 -> Pair (Pair (S n3) (Cons (Pair (CP_user
                          n3) (CS_alts als2)) (app cs2 cs3))) (Case0 fe
                          (CP_user n3))))))

type App_stat = Nat

type Cons_stat = Set (Prod Constructor Nat)

type Statistics = Prod App_stat Cons_stat

cons_times_nat_eq_dec :: (Prod Constructor Nat) -> (Prod Constructor 
                         Nat) -> Sumbool
cons_times_nat_eq_dec a b =
  prod_rec (\a0 b0 b1 ->
    case b1 of
      Pair c n ->
        sumbool_rec (\_ ->
          eq_rec_r c
            (sumbool_rec (\_ -> eq_rec_r n Left b0) (\_ -> Right)
              (eq_nat_dec b0 n)) a0) (\_ -> Right) (eq_nat_dec a0 c)) a b

gather_stats :: Expr1 -> Statistics
gather_stats e =
  expr_rect (\v v0 c -> Pair (length v0) Nil) (\c v c0 -> Pair O (Cons (Pair
    c (length v)) Nil)) (\l e0 iHe -> iHe) (\e0 iHe c -> iHe) e

gather_stats_csn :: Cs_node -> Statistics
gather_stats_csn csn =
  case csn of
    CS_expr e -> gather_stats e
    CS_lf l ->
      (case l of
         Lf u v b e ->
           (case gather_stats e of
              Pair spap scons -> Pair (max spap b) scons))
    _ -> Pair O Nil

stat_sum :: Statistics -> Statistics -> Statistics
stat_sum a b =
  case a of
    Pair apap acons ->
      (case b of
         Pair bpap bcons -> Pair (max apap bpap)
           (set_union cons_times_nat_eq_dec acons bcons))

gather_stats_cs :: Code_store -> Statistics
gather_stats_cs cs =
  list_rect (Pair O Nil) (\a cs0 iHcs ->
    case a of
      Pair cp csn -> stat_sum (gather_stats_csn csn) iHcs) cs

impl_for_pap :: App_stat -> Code_store
impl_for_pap n =
  case n of
    O -> Cons (Pair (CP_pap O) (CS_lf (Lf Dont_update Nil O (App0 (C_ind O)
      (map (\x -> C_ind x) (from (S O) O)) O)))) Nil
    S m -> Cons (Pair (CP_pap n) (CS_lf (Lf Dont_update Nil O (App0 (C_ind O)
      (map (\x -> C_ind x) (from (S O) n)) O)))) (impl_for_pap m)

impl_for_cons :: Cons_stat -> Code_store
impl_for_cons xs =
  case xs of
    Nil -> Nil
    Cons p xs0 ->
      (case p of
         Pair c n -> Cons (Pair (CP_cons c n) (CS_lf (Lf Dont_update Nil O
           (Constr0 c (map (\x -> C_ind x) (from O n)) O))))
           (impl_for_cons xs0))

verify :: Expr0 -> Code_store -> Expr1 -> Sumbool
verify e cs e_fla =
  expr_rec2 (\x xs cu cs0 e_fla0 ->
    case e_fla0 of
      App0 v v0 c ->
        (case var_eq_dec v x of
           Left ->
             (case vars_eq_dec v0 xs of
                Left ->
                  (case eq_nat_dec c cu of
                     Left ->
                       eq_rec_r cu (eq_rec_r xs (eq_rec_r x Left v) v0) c
                     Right -> Right)
                Right -> Right)
           Right -> Right)
      _ -> Right) (\c xs cu cs0 e_fla0 ->
    case e_fla0 of
      Constr0 c0 v c1 ->
        (case eq_nat_dec c0 c of
           Left ->
             (case vars_eq_dec v xs of
                Left ->
                  (case eq_nat_dec c1 cu of
                     Left ->
                       eq_rec_r cu (eq_rec_r xs (eq_rec_r c Left c0) v) c1
                     Right -> Right)
                Right -> Right)
           Right -> Right)
      _ -> Right) (\e0 lfs iHe lF cs0 e_fla0 ->
    case e_fla0 of
      Letrec0 l e_fla1 ->
        (case iHe cs0 e_fla1 of
           Left ->
             (case eq_nat_dec (length l) (length lfs) of
                Left ->
                  unsafeCoerce
                    (list_rec (\lF0 l0 _ ->
                      case l0 of
                        Nil -> Left
                        Cons p l1 -> false_rec __) (\a lfs0 iHlfs lF0 l0 _ ->
                      case l0 of
                        Nil -> false_rec __
                        Cons p l1 ->
                          (case a of
                             Lf u v b e1 ->
                               (case p of
                                  Pair v0 c ->
                                    (case iHlfs (\lf _ -> lF0 lf __) l1 __ of
                                       Left ->
                                         (case vars_eq_dec v v0 of
                                            Left ->
                                              eq_rec_r v0 (\lF1 ->
                                                case find_cs cs0 c of
                                                  CS_lf l2 ->
                                                    (case l2 of
                                                       Lf u0 v1 b0 e2 ->
                                                         (case lF0 a __ cs0
                                                                 e2 of
                                                            Left ->
                                                              (case upd_flag_eq_dec
                                                                    u0 u of
                                                                 Left ->
                                                                   (case 
                                                                    vars_eq_dec
                                                                    v0 v1 of
                                                                      
                                                                    Left ->
                                                                      (case 
                                                                      eq_nat_dec
                                                                      b0 b of
                                                                      
                                                                      Left ->
                                                                        eq_rec_r
                                                                        b (\_ ->
                                                                        eq_rec_r
                                                                        v1
                                                                        (\lF2 ->
                                                                        eq_rec_r
                                                                        u (\_ ->
                                                                        Left) u0
                                                                        __) v0
                                                                        lF1) b0
                                                                        __
                                                                      
                                                                      Right ->
                                                                        Right)
                                                                      
                                                                    Right ->
                                                                      Right)
                                                                 Right ->
                                                                   Right)
                                                            Right -> Right))
                                                  _ -> Right) v lF0
                                            Right -> Right)
                                       Right -> Right)))) lfs) lF l __
                Right -> Right)
           Right -> Right)
      _ -> Right) (\e0 als iHe aLS cs0 e_fla0 ->
    case e_fla0 of
      Case0 e_fla1 c ->
        (case find_cs cs0 c of
           CS_alts a ->
             (case iHe cs0 e_fla1 of
                Left ->
                  (case eq_nat_dec (length a) (length als) of
                     Left ->
                       unsafeCoerce
                         (list_rec (\aLS0 als_fla _ -> Left)
                           (\a0 als0 iHals aLS0 als_fla _ ->
                           case als_fla of
                             Nil -> false_rec __
                             Cons a1 als_fla0 ->
                               (case a0 of
                                  Alt b e1 ->
                                    (case a1 of
                                       Alt b0 c0 ->
                                         (case find_cs cs0 c0 of
                                            CS_expr e2 ->
                                              (case aLS0 a0 __ cs0 e2 of
                                                 Left ->
                                                   (case iHals (\al _ ->
                                                           aLS0 al __)
                                                           als_fla0 __ of
                                                      Left ->
                                                        (case eq_nat_dec b b0 of
                                                           Left ->
                                                             eq_rec_r b0
                                                               (\aLS1 ->
                                                               Left) b aLS0
                                                           Right -> Right)
                                                      Right -> Right)
                                                 Right -> Right)
                                            _ -> Right)))) als) aLS a __
                     Right -> Right)
                Right -> Right)
           _ -> Right)
      _ -> Right) e cs e_fla

compile :: Expr0 -> Option (Prod (Prod Code_store Expr1) Statistics)
compile d_e =
  case flatten O d_e of
    Pair p e ->
      (case p of
         Pair n cs ->
           (case gather_stats e of
              Pair stats_e_app stats_e_cons ->
                (case gather_stats_cs cs of
                   Pair stats_cs_app stats_cs_cons ->
                     let stats_final_app = max stats_e_app stats_cs_app in
                     let
                          stats_final_cons = set_union cons_times_nat_eq_dec
                                               stats_e_cons stats_cs_cons
                     in
                     let
                          cs_final = app (impl_for_pap stats_final_app)
                                       (app (impl_for_cons stats_final_cons)
                                         cs)
                     in
                     (case verify d_e cs_final e of
                        Left -> Some (Pair (Pair cs_final e) (Pair
                          stats_final_app stats_final_cons))
                        Right -> None))))


