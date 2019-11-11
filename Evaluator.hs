{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

module Evaluator where

import Prelude hiding (round, head)

import qualified Data.Set as S
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Head)
import           Data.Type.Equality hiding (type (==))

import Types
import Set
import Unification

type Solution = S.Set Tuple

findUnifiers :: Atom modes terms -> Solution -> S.Set (SomeUnifier (KeepVars terms))
findUnifiers atom solution = catMaybes $ S.map (unify atom) solution
  where
  catMaybes :: S.Set (Maybe (SomeUnifier vars)) -> S.Set (SomeUnifier vars)
  catMaybes f = foldr `flip` mempty `flip` f
              $ \mEl acc -> maybe acc (`S.insert` acc) mEl

step :: Solution -> Clause -> Solution
step solution (Clause head clauseBody rangeRestriction) =
  (`S.map` walkBody clauseBody) $ \(SU unifier Refl) ->
    deriveHead head unifier rangeRestriction
  where
  walkBody :: Body vars -> S.Set (SomeUnifier vars)
  walkBody BEmpty = S.singleton (SU SNil Refl)
  walkBody (BSnoc body atom@(Atom _ terms) _ _) = S.unions $
    (`S.map` walkBody body) $ \(SU unifier Refl) ->
      (`S.map` findUnifiers (substAtom atom unifier) solution) $ \(SU extension Refl) ->
        case sym $ lemConcatHomo (Sing @_ @SubstVarSym0) extension unifier of
          Refl -> case lemSubstOnVars terms unifier of
            Refl -> SU (extension %++ unifier) Refl

deriveHead :: Head terms -> Unifier substs
           -> Subseteq (KeepVars terms) (Map SubstVarSym0 substs) :~: 'True
           -> Tuple
deriveHead (Head atom@(Atom _ terms) _) unifier subseteq =
  case substAtom atom unifier of
    head' -> Tuple head' (lemCompleteSubst terms unifier subseteq)

lemCompleteSubst :: STerms terms -> Unifier substs
                 -> Subseteq (KeepVars terms) (Map SubstVarSym0 substs) :~: 'True
                 -> KeepVars (SubstTerms terms substs) :~: '[]
lemCompleteSubst terms substs subseteq
  | Refl <- lemSubstOnVars terms substs
  , Refl <- lemExhaust (sKeepVars terms) (sMap (sing @SubstVarSym0) substs) subseteq = Refl

round :: Program -> Solution -> Solution
round program solution = mconcat (map (step solution) program)
                      <> solution

evaluator :: Program -> Solution -> Solution
evaluator program solution =
  if newSolution == solution
    then solution
    else evaluator program newSolution
  where
  newSolution = round program solution
