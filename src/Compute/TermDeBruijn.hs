module Compute.TermDeBruijn where

-- data Var = V Int deriving Show

data Tm = VAR Int | NAT | UNIT | SIG Tm Tm | PI Tm Tm | UNI Int | EQUAL Tm Tm Tm
        | Z | S Tm | TT | PROD Tm Tm | LAM Tm | REFL
        | SPREAD Tm Tm | APP Tm Tm | NATREC Tm Tm Tm
        deriving (Eq,Show)

-- lift e c k = lift vars in e by k from c
lift :: Tm -> Int -> Int -> Tm
lift (VAR n) c k
  | n < c           = VAR n
  | otherwise       = VAR (n + k)
lift NAT _ _        = NAT
lift UNIT _ _       = UNIT
lift (SIG a b) c k  = SIG (lift a c k) (lift b (c + 1) k)
lift (PI a b) c k   = PI (lift a c k) (lift b (c + 1) k)
lift (UNI i) c k    = UNI i
lift (EQUAL e1 e2 a) c k = EQUAL (lift e1 c k) (lift e2 c k) (lift a c k)
lift Z _ _            = Z
lift (S e) c k        = S (lift e c k)
lift TT _ _           = TT
lift (PROD e1 e2) c k = PROD (lift e1 c k) (lift e2 c k)
lift (LAM e) c k      = LAM (lift e (c + 1) k)
-- SPREAD introduces two new bindings for `e` to play with
lift (SPREAD e p) c k   = SPREAD (lift e (c + 2) k) (lift p c k)
lift (APP e1 e2) c k    = APP (lift e1 c k) (lift e2 c k)
-- NATREC also binds two new variables (the recursive call and the current number)
lift (NATREC ez es e) c k = NATREC (lift ez c k) (lift es (c + 2) k) (lift e c k)

recbind :: Int -> Tm -> Int -> Tm -> Tm
recbind n m x e = subst e (x + n) (lift m 0 n)

-- subst m x e == [m/x] e
subst :: Tm -> Int -> Tm -> Tm
subst m x (VAR y)
  | y < x        = VAR y
  | y == x       = m
  | otherwise    = VAR (y - 1)
subst _ _ NAT    = NAT
subst _ _ UNIT   = UNIT
subst m x (SIG a b)   = SIG (subst m x a) (recbind 1 m x b)
subst m x (PI a b)    = PI (subst m x a) (recbind 1 m x b)
subst _ _ (UNI i)     = UNI i
subst m x (EQUAL e1 e2 a) = EQUAL (subst m x e1) (subst m x e2) (subst m x a)
subst _ _ Z       = Z
subst m x (S e)       = S (subst m x e)
subst _ _ TT      = TT
subst m x (PROD e1 e2) = PROD (subst m x e1) (subst m x e2)
subst m x (LAM e) = LAM (recbind 1 m x e)
subst m x (SPREAD e p) = SPREAD (recbind 2 m x e) (subst m x p)
subst m x (APP e1 e2)  = APP (subst m x e1) (subst m x e2)
subst m x (NATREC ez es e) = NATREC (subst m x ez) (recbind 2 m x es) (subst m x e)


-- wellformed n e == the term is wellformed under n free variables
wellformed :: Int -> Tm -> Bool
wellformed n (VAR x) = x < n && x >= 0
wellformed n NAT     = True
wellformed n UNIT    = True
wellformed n (SIG a b) = wellformed n a && wellformed (n + 1) b
wellformed n (PI a b)  = wellformed n a && wellformed (n + 1) b
wellformed n (UNI i)    = i >= 0
wellformed n (EQUAL e1 e2 a) = wellformed n e1 && wellformed n e2 && wellformed n a
wellformed n Z         = True
wellformed n (S e)     = wellformed n e
wellformed n TT        = True
wellformed n (PROD e1 e2) = wellformed n e1 && wellformed n e2
wellformed n (LAM e)      = wellformed (n + 1) e
wellformed n (SPREAD e p) = wellformed (n + 2) e && wellformed n p
wellformed n (APP e1 e2)  = wellformed n e1 && wellformed n e2
wellformed n (NATREC ez es e) = wellformed n ez && wellformed (n + 2) es && wellformed n e

closed :: Tm -> Bool
closed = wellformed 0

-- s = \x \y \z . x z (y z)
-- s = \\\. 2 0 (1 0)
s = LAM (LAM (LAM (APP (APP (VAR 2) (VAR 0)) (APP (VAR 2) (VAR 1)))))

-- k = \x \y . x
-- k = \\.1
k = LAM (LAM (VAR 1))

-- i = \x . x
i = LAM (VAR 0)


-- beta
beta :: Tm -> Tm
beta e
  | wellformed 0 e =
    case e of
      APP (LAM e1) e2 -> subst e2 0 e1
      APP e1 e2 -> APP (beta e1) e2
      SPREAD e (PROD e1 e2) -> subst e2 1 (subst e1 0 e)
      SPREAD e1 e2 -> SPREAD e1 (beta e2)
      NATREC ez es Z        -> ez
      NATREC ez es (S e)        -> subst e 1 (subst (NATREC ez es e) 0 es)
      NATREC e1 e2 e3 -> NATREC e1 e2 (beta e3)
