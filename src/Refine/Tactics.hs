{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
module Refine.Tactics where

import Compute.TermDeBruijn
import Refine.Context


-- derivations for building up constructive contents
-- i.e. the computational content
data Derivation where
  -- general derivations
  Hyp :: Int -> Derivation
  -- don't know why they call typehood (formation) introduction rules

  -- H >> U_i
  IntroUni :: Derivation
  -- >> U_i = U_j
  EqUni :: Derivation

  -- H >> NAT
  IntroNat :: Derivation
  -- H >> Z = Z (in Nat)
  EqZ     :: Derivation
  -- H >> S n = S n' (in Nat)
  --   >> n = n' (in Nat)
  EqS     :: Derivation -> Derivation -- [n = m] \to [S n = S m]


  -- H >> Sig x : A . B
  --   H >> A
  --   H, a : A >> [a/x]B
  IntroSig :: Derivation -> Derivation -> Derivation
  -- >> \Sig x : A . B = \Sig x : A' . B'
  --    >> A = A'
  --    >> [a/x]B = [a/x]B'
  EqSig :: Derivation -> Derivation -> Derivation

  -- H >> Pi x : A . B
  --   H >> A
  --   H, a : A >> [a/x]B
  IntroPi :: Derivation -> Derivation -> Derivation
  -- >> \Pi x : A . B = \Pi x : A' . B'
  --   >> A = A'
  --   >> [a/x]B = [a/x]B'
  EqPi :: Derivation -> Derivation -> Derivation

  IntroUnit :: Derivation
  EqTT    :: Derivation
  -- EqPr    :: Derivation -> Derivation -> Derivation


-- the refinement judgment
-- H >> e = e : A
-- H is the refinement context, e is the term to be refined to type A

-- here c is the context
data Judgment where
  Judgment :: (Telescope c) => c -> Tm -> Judgment

-- tactic combinators and refinement rules

class Tactical t where
  idTAC :: t
  thenTAC :: t -> t -> Judgment -> TacticRet
  thenTACL :: t -> [t] -> Judgment -> TacticRet
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
  thenTAC t1 t2 j =
    let TR { subgoals = gls , extract = ext } = runTAC t1 j
        rets = map (runTAC t2) gls
        gls' = map subgoals rets
        exts = map extract rets
    in
      TR { subgoals = concat gls'
         , extract = \l -> ext $ zipWith (\f x -> f x) exts (split gls' l) }
  thenTACL t1 tl j =
    let TR { subgoals = gls , extract = ext } = runTAC t1 j
        rets = (map runTAC tl) <*> gls
        gls' = map subgoals rets
        exts = map extract rets
    in
      TR { subgoals = concat gls'
         , extract = \l -> ext $ zipWith (\f x -> f x) exts (split gls' l) }



data TacticRet = TR { subgoals :: [Judgment] , extract :: [Derivation] -> Derivation }

instance Show Judgment where
  show (Judgment c e) = show c ++ " >> " ++ show e

instance Show TacticRet where
  show TR { subgoals = js , extract = fs } = "subgoals: " ++ show js
