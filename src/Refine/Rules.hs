module Rules where

import Refine.Tactics
import Compute.TermDeBruijn
import Refine.Context

-- refinement rules!!!!
-- UNIT typehood
introUNIT :: Judgment -> TacticRet
introUNIT (Judgment c UNIT) = TR { subgoals = [] , extract = const IntroUnit }
introUNIT _                    = error "intro UNIT does not apply!!"

-- NAT typehood
introNAT :: Judgment -> TacticRet
introNAT (Judgment c NAT) = TR { subgoals = [] , extract = const IntroNat }
introNAT _                  = error "intro NAT does not apply!!"

-- SIG typehood at universe level i
introSig :: Int -> Judgment -> TacticRet
introSig i (Judgment c (SIG a b)) =
  TR { subgoals = [ Judgment c (EQUAL a a (UNI i)) , Judgment (extend 0 a c) b ]
     , extract = \(ea:eb:_) -> IntroSig ea eb }
introSig _ _   = error "intro SIG does not apply!!!!"

-- PI typehood
introPi :: Int -> Judgment -> TacticRet
introPi i (Judgment c (PI a b)) =
  TR { subgoals = [ Judgment c (EQUAL a a (UNI i)) , Judgment (extend 0 a c) b ]
     , extract = \(ea:eb:_) -> IntroPi ea eb }
introPi _ _    = error "intro PI does not apply!!"

-- membership equality in Nat
zEqInNat :: Judgment -> TacticRet
zEqInNat (Judgment c (EQUAL Z Z NAT)) = TR { subgoals = [] , extract = const EqZ }
zEqInNat _                            = error "eq z does not apply!!!"

sEqInNat :: Judgment -> TacticRet
sEqInNat (Judgment c (EQUAL (S e) (S e') NAT)) =
  TR { subgoals = [ Judgment c (EQUAL e e' NAT)] , extract = \(ee:_) -> EqS ee }
sEqInNat _  = error "eq s(-) does not apply!!"

ttEqInUnit :: Judgment -> TacticRet
ttEqInUnit (Judgment c (EQUAL TT TT UNIT)) = TR { subgoals = [] , extract = \_ -> EqTT }
ttEqInUnit _                               = error "eq tt does not apply!!"
