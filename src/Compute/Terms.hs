{-# LANGUAGE DeriveFunctor, TypeOperators #-}
module Terms where

data Expr f = In (f (Expr f))

data Var e = V Int
         deriving (Functor, Show)

data Tm e = NAT | UNIT | SIG e e e | PI e e | UNI Int | EQ e e e
          | Z | S e | TT | PROD e e | LAM e | REFL
          | SPREAD e e | APP e e | NATREC e e e
          deriving (Functor,Show)

infix 7 :+:
data (f :+: g) e = Inl (f e) | Inr (g e)

type EXP = Expr (Var :+: Tm)

class Functor f => Eval f where
  beta :: f (Expr f) -> f (Expr f)
  subst :: f (Expr f) -> Int -> f (Expr f) -> f (Expr f)


instance Eval Var where
  beta x = x
  subst m x (V y)
    | x == y    = m
    | otherwise = V y

-- Tm (Expr Tm) -> Tm (Expr Tm)
instance Eval Tm where
  beta (APP (In (SPREAD (In e1) (In e2))) (In (PROD (In p1) (In p2)))) = undefined
  beta (APP (In (NATREC (In ez) (In es) (In e))) (In Z)) = undefined
  beta (APP (In (NATREC (In ez) (In es) (In e))) (In (S (In n)))) = undefined
  beta (APP (In (LAM (In e1))) (In e2)) = undefined
  beta x = x
  subst = undefined
  -- subst m x
