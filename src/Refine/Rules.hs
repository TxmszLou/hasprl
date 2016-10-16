module Rules where

import Refine.Tactics
import Compute.TermDeBruijn
import Refine.Context

-- refinement rules!!!!

-- general rules
hyp :: Int -> Tactic
hyp x = T $
  \j ->
    case j of
      (Judgment c a) ->
        case get x c of
          Just a' -> if a == a'
                     then TR { subgoals = [] , extract = const (Hyp x) }
                     else error $ "Hyp " ++ show x ++ " has type " ++ show a'
                          ++ ", incompatible with goal type " ++ show a
          Nothing -> error "Hyp not found!!"

hypEq :: Int -> Tactic
hypEq x = T $
  \j ->
    case j of
      Judgment c (EQUAL e1 e2 a)
        | VAR x /= e1   -> error $ "LHS is " ++ show e1 ++ " rather than " ++ show (VAR x)
        | VAR x /= e2   -> error $ "RHS is " ++ show e2 ++ " rather than " ++ show (VAR x)
        | otherwise     ->
          case get x c of
            Just a'   ->
              if a /= a'
              then error $ "type " ++ show a ++ " expected, given " ++ show a'
              else TR { subgoals = [] , extract = const (HypEq x) }
            Nothing -> error "Hyp not found!!"
      _             -> error "hypEq does not apply!!"

-- typehood
-- UNIT typehood
introUNIT :: Tactic
introUNIT = T $
  \j ->
    case j of
      (Judgment c UNIT) -> TR { subgoals = [] , extract = const IntroUnit }
      _                 -> error "intro UNIT does not apply!!"

-- NAT typehood
introNAT :: Tactic
introNAT = T $
  \j ->
    case j of
      (Judgment c NAT) -> TR { subgoals = [] , extract = const IntroNat }
      _                -> error "intro NAT does not apply!!"

natEq :: Tactic
natEq = T $
  \j ->
    case j of
      (Judgment c (EQUAL NAT NAT (UNI _))) -> TR { subgoals = [] , extract = const EqNat }
      _ -> error "NAT type equality does not apply!!"

-- SIG typehood at universe level i
introSig :: Int -> Tactic
introSig i = T $
  \j ->
    case j of
      (Judgment c (SIG a b)) ->
        TR { subgoals = [ Judgment c (EQUAL a a (UNI i)) , Judgment (extend 0 a c) b ]
           , extract = \(ea:eb:_) -> IntroSig ea eb }
      _                      ->  error "intro SIG does not apply!!!!"

-- PI typehood
introPi :: Int -> Tactic
introPi i = T $
  \j ->
    case j of
      (Judgment c (PI a b)) ->
        TR { subgoals = [ Judgment c (EQUAL a a (UNI i)) , Judgment (extend 0 a c) b ]
           , extract = \(ea:eb:_) -> IntroPi ea eb }
      _                     -> error "intro PI does not apply!!"

-- membership equality in PI
lamEqInPi :: Int -> Tactic
lamEqInPi i = T $
  \j ->
    case j of
      (Judgment c (EQUAL (LAM e) (LAM e') (PI a b))) ->
        TR { subgoals = [ Judgment (extend 0 a c) (EQUAL (lift e 0 1) (lift e' 0 1) b) , Judgment c (EQUAL a a (UNI i))]
           , extract = \(ee:ea:_) -> EqLam ee ea }
      _                    -> error "lambda equality does not apply!!"

-- membership equality in Nat
zEqInNat :: Tactic
zEqInNat = T $
  \j ->
    case j of
      (Judgment c (EQUAL Z Z NAT)) -> TR { subgoals = [] , extract = const EqZ }
      _                            -> error "eq z does not apply!!!"

sEqInNat :: Tactic
sEqInNat = T $
  \j ->
    case j of
      (Judgment c (EQUAL (S e) (S e') NAT)) ->
        TR { subgoals = [ Judgment c (EQUAL e e' NAT)]
           , extract = \(ee:_) -> EqS ee }
      _       -> error "eq s(-) does not apply!!"

ttEqInUnit :: Tactic
ttEqInUnit = T $
  \j ->
    case j of
      (Judgment c (EQUAL TT TT UNIT)) -> TR { subgoals = [] , extract = const EqTT }
      _                               -> error "eq tt does not apply!!"


-- test tactics
idx :: Judgment
idx = Judgment ([UNI 0] :: LCtxt) (EQUAL (LAM (VAR 0)) (LAM (VAR 0)) (PI (VAR 0) (VAR 0)))

proveIdx :: Tactic
proveIdx = thenTACL (lamEqInPi 0) [hypEq 1 , hypEq 0]

hypy :: Judgment
hypy = Judgment [UNI 0 , NAT] NAT

refOne :: Judgment
refOne = Judgment ([] :: LCtxt) (EQUAL (S Z) (S Z) NAT)

prog :: Tactic
prog = thenTAC sEqInNat zEqInNat
