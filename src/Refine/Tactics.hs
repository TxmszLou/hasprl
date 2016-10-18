{-# LANGUAGE GADTs #-}
module Refine.Tactics where

import Compute.TermDeBruijn
import Refine.Context


-- derivations for building up constructive contents
-- i.e. the computational content
data Derivation where
  -- general derivations
  Hyp :: Int -> Derivation
  HypEq :: Int -> Derivation

  -- UNIT
  IntroUnit :: Derivation
  EqUnit    :: Derivation
  EqTT      :: Derivation

  -- NAT
  -- H >> NAT
  IntroNat :: Derivation
  EqNat    :: Derivation
  -- H >> Z = Z (in Nat)
  EqZ     :: Derivation
  -- H >> S n = S n' (in Nat)
  --   >> n = n' (in Nat)
  EqS     :: Derivation -> Derivation -- [n = m] \to [S n = S m]

  -- UNI
  -- H >> U_i
  IntroUni :: Derivation
  -- >> U_i = U_j
  EqUni :: Derivation

  -- PI
  -- H >> Pi x : A . B
  --   H >> A
  --   H, a : A >> [a/x]B
  IntroPi :: Derivation -> Derivation -> Derivation
  -- >> \Pi x : A . B = \Pi x : A' . B'
  --   >> A = A'
  --   >> [a/x]B = [a/x]B'
  EqPi :: Derivation -> Derivation -> Derivation
  -- >> lam x . e = lam x . e' in Pi x : A , B
  --   a : A >> [a/x]e = [a/x]e' in [a/x]B
  --   >> A in U_i
  EqLam :: Derivation -> Derivation -> Derivation

  -- SIG
  -- H >> Sig x : A . B
  --   H >> A
  --   H, a : A >> [a/x]B
  IntroSig :: Derivation -> Derivation -> Derivation
  -- >> \Sig x : A . B = \Sig x : A' . B'
  --    >> A = A'
  --    >> [a/x]B = [a/x]B'
  EqSig :: Derivation -> Derivation -> Derivation
  -- >> (a,b) = (a',b') : Sig x : A . B
  --   >> a = a : A
  --   >> b = b : [a/x]B
  EqPr  :: Derivation -> Derivation -> Derivation


  -- EqPr    :: Derivation -> Derivation -> Derivation


-- the refinement judgment
-- H >> e = e : A
-- H is the refinement context, e is the term to be refined to type A

-- here c is the context
data Judgment where
  Judgment :: (Telescope c) => c -> Tm -> Judgment

data TacticRet = TR { subgoals :: [Judgment] , extract :: [Derivation] -> Derivation }

-- tactic combinators and refinement rules
class Tactical t where
  idTAC :: t
  thenTAC :: t -> t -> t
  thenTACL :: t -> [t] -> t
  -- orelseTAC :: t -> t -> Judgment -> TacticRet

-- data SimpleTac = Id | Intro (Judgment -> TacticRet) | Elim Tm | Eq | Fail
--             deriving (Eq,Show)

newtype Tactic = T { runTAC :: Judgment -> TacticRet }

split :: [[a]] -> [b] -> [[b]]
split [] ys = []
split (x:xs) ys =
  let len = length x
  in (take len ys) : split xs (drop len ys)

instance Tactical Tactic where
  idTAC = T (\j -> TR { subgoals = [j] , extract = \[d] -> d })
  thenTAC t1 t2 = T $
    \j ->
      let TR { subgoals = gls , extract = ext } = runTAC t1 j
          rets = map (runTAC t2) gls
          gls' = map subgoals rets
          exts = map extract rets
      in
        TR { subgoals = concat gls'
         , extract = \l -> ext $ zipWith ($) exts (split gls' l) }
  thenTACL t1 tl = T $
    \j ->
      let TR { subgoals = gls , extract = ext } = runTAC t1 j
          -- rets = ((map runTAC tl) :: [Judgment -> TacticRet]) <*> (gls :: [Judgment])
          rets = zipWith ($) (map runTAC tl) gls
          gls' = map subgoals rets
          exts = map extract rets
      in
        TR { subgoals = concat gls'
           , extract = \l -> ext $ zipWith ($) exts (split gls' l) }


instance Show Judgment where
  show (Judgment c e) = show c ++ " >> " ++ show e

instance Show TacticRet where
  show TR { subgoals = js , extract = fs } = "subgoals: " ++ show js
