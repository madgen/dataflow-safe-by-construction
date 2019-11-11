{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}

module Evaluator where

import Prelude hiding (round, head, pred)

import qualified Data.Set as S
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Singletons.Prelude hiding (Head)
import           Data.Type.Equality hiding (type (==))

import Types
import Set
import Unification

type Solution = S.Set Tuple

findUnifiers :: Atom modes polarity terms -> Solution -> S.Set (SomeUnifier (KeepVars terms))
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
  walkBody (BSnoc body atom@(Atom _ _ terms) _ _) = S.unions $
    (`S.map` walkBody body) $ \(SU unifier Refl) ->
      (`S.map` findUnifiers (substAtom atom unifier) solution) $ \(SU extension Refl) ->
        case sym $ lemConcatHomo (Sing @_ @SubstVarSym0) extension unifier of
          Refl -> case lemSubstOnVars terms unifier of
            Refl -> SU (extension %++ unifier) Refl

deriveHead :: Head terms -> Unifier substs
           -> Subseteq (KeepVars terms) (Map SubstVarSym0 substs) :~: 'True
           -> Tuple
deriveHead (Head atom@(Atom _ _ terms) _) unifier subseteq =
  case substAtom atom unifier of
    head' -> Tuple head' (lemCompleteSubst terms unifier subseteq)

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

-- Tests

type Pure2 = '[ 'DontCare, 'DontCare ]

ancestorP, parentP :: Predicate Pure2
ancestorP = Predicate "ancestor" sing
parentP   = Predicate "parent" sing

atom2Gen :: Predicate Pure2
         -> SPolarity polarity
         -> STerm term -> STerm term'
         -> Atom Pure2 polarity '[term, term']
atom2Gen pred polarity t1 t2 = Atom pred polarity (t1 `SCons` t2 `SCons` SNil)

ancestorA, parentA :: SPolarity polarity
                   -> STerm term -> STerm term'
                   -> Atom Pure2 polarity '[term, term']
ancestorA = atom2Gen ancestorP
parentA   = atom2Gen parentP

tuple2Gen :: Predicate Pure2 -> SSymbol sym1 -> SSymbol sym2 -> Tuple
tuple2Gen pred s1 s2 = Tuple
  (Atom pred SPositive (STLit (SLit s1) `SCons` STLit (SLit s2) `SCons` SNil))
  Refl

ancestorT, parentT :: SSymbol sym1 -> SSymbol sym2 -> Tuple
ancestorT = tuple2Gen ancestorP
parentT   = tuple2Gen parentP

ancestorProgram :: Program
ancestorProgram =
  case traverse (uncurry mkClause) clauseCandidates of
    Right clauses -> clauses
    Left err -> error err
  where
  clauseCandidates =
    [ ( SA $ ancestorA SPositive (STVar (SVar $ sing @"X")) (STVar (SVar $ sing @"Y"))
      , [ SA $ parentA SPositive (STVar (SVar $ sing @"X")) (STVar (SVar $ sing @"Y")) ])
    , ( SA $ ancestorA SPositive (STVar (SVar $ sing @"X")) (STVar (SVar $ sing @"Y"))
      , [ SA $ ancestorA SPositive (STVar (SVar $ sing @"X")) (STVar (SVar $ sing @"T"))
        , SA $ ancestorA SPositive (STVar (SVar $ sing @"T")) (STVar (SVar $ sing @"Y"))
        ])
    ]

input :: Solution
input = S.fromList
  [ parentT (sing @"Nilufer") (sing @"Mistral")
  , parentT (sing @"Laurent") (sing @"Mistral")
  , parentT (sing @"Hulusi") (sing @"Emir")
  , parentT (sing @"Nazli") (sing @"Emir")
  , parentT (sing @"Orhan") (sing @"Hulusi")
  , parentT (sing @"Orhan") (sing @"Nilufer")
  ]

expected :: Solution
expected = input <> S.fromList
  [ ancestorT (sing @"Nilufer") (sing @"Mistral")
  , ancestorT (sing @"Laurent") (sing @"Mistral")
  , ancestorT (sing @"Hulusi") (sing @"Emir")
  , ancestorT (sing @"Nazli") (sing @"Emir")
  , ancestorT (sing @"Orhan") (sing @"Hulusi")
  , ancestorT (sing @"Orhan") (sing @"Nilufer")
  , ancestorT (sing @"Orhan") (sing @"Emir")
  , ancestorT (sing @"Orhan") (sing @"Mistral")
  ]

ancestorTest :: IO ()
ancestorTest =
  if output == expected
    then putStrLn "Ancestor runs successfully"
    else do
      putStrLn "Ancestor program failed. Here's the output: "
      print output
  where
  output = evaluator ancestorProgram input
