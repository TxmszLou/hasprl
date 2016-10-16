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
hypx :: Judgment
hypx = Judgment [UNI 0] (UNI 0)

-- runTAC (hyp 0) hypx
-- => subgoals : []

hypy :: Judgment
hypy = Judgment [UNI 0 , NAT] NAT
