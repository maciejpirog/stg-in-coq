module User where

import Core

c = putStrLn . printR . compile

printR :: Option (Prod (Prod Code_store Expr1) Statistics) -> String
printR None = "\n\n\tERROR!!\n\n"
printR (Some (Pair (Pair cs e) stat)) = "\nCODE STORE:\n\n" ++ printCs cs ++ "\nEXPRESSION:\n\n" ++ show e

printCs Nil = ""
printCs (Cons (Pair cp csn) xs) = show cp ++ " -->\n" ++ show csn ++ "\n\n" ++ printCs xs

fromList :: [a] -> List a
fromList [] = Nil
fromList (x : xs) = Cons x $ fromList xs

fromInt :: Int -> Nat
fromInt 0 = O
fromInt x = S (fromInt $ x-1)

cons1, cons2, cons3 :: Expr
cons1 = Constr O Nil O
cons2 = Constr O (fromList [C_ind $ fromInt 0, C_ind $ fromInt 1, B_ind $ fromInt 0, B_ind $ fromInt 4]) O
cons3 = Constr (fromInt 4) Nil O

app1, app2, app3 :: Expr
app1 = App (B_ind $ fromInt 3) Nil O
app2 = App (B_ind $ fromInt 0) (fromList [C_ind $ fromInt 2, B_ind $ fromInt 2]) O
app3 = App (B_ind $ fromInt 1) (fromList [B_ind $ fromInt 0]) O

lf1, lf2 :: Lambda_form
lf1 = Lf Dont_update Nil O cons1
lf2 = Lf Dont_update (fromList [B_ind O, B_ind (S O)]) (fromInt 2) app2

let1 :: Expr
let1 = Letrec (fromList [lf1, lf2]) app1

case1 :: Expr
case1 = Case let1 $ fromList [Alt (fromInt 2) let1, Alt O cons2, Alt O cons3]

lf3, lf4 :: Lambda_form
lf3 = Lf Update Nil (fromInt 7) $ Case case1 $ fromList [Alt O case1, Alt O let1]
lf4 = Lf Update Nil O case1

let2 :: Expr
let2 = Letrec (fromList [lf1, lf3, lf4]) case1


