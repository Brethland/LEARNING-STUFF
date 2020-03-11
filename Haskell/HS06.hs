module Exp where

data Exp =
      Const Double
    | Symbol String
    | Add Exp Exp
    | Mul Exp Exp
    deriving Show

d :: Exp -> String -> Exp
d (Const   _) _ = Const 0
d (Symbol  s) t = if s == t then Const 1 else Const 0
d (Add e1 e2) t = (d e1 t) `Add` (d e2 t)
d (Mul e1 e2) t = (Mul e1 (d e2 t)) `Add` (Mul e2 (d e1 t))

x :: Exp
x = Symbol "x"

e :: Exp
e = (x `Mul` x) `Add` (Const 1)

edx :: Exp
edx = e `d` "x"