{-# LANGUAGE GADTs #-}
module Refine.Tactics where

import Compute.TermDeBruijn
import Refine.Context


-- derivations for building up constructive contents
-- i.e. the computational content
data Derivation where
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

data Tactic = Id | Intro Tm | Elim Tm | Eq | Fail | Hyp
            deriving (Eq,Show)

data TacticRet = TR { subgoals :: [Judgment] , extract :: [Derivation] -> Derivation }

instance Show Judgment where
  show (Judgment c e) = show c ++ " >> " ++ show e

instance Show TacticRet where
  show TR { subgoals = js , extract = fs } = "subgoals: " ++ show js
