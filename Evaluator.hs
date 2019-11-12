{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
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

findUnifiers :: Solution -> Atom modes 'Positive terms -> S.Set (SomeUnifier (KeepVars terms))
findUnifiers solution atom = catMaybes $ S.map (unify atom) solution
  where
  catMaybes :: S.Set (Maybe (SomeUnifier vars)) -> S.Set (SomeUnifier vars)
  catMaybes f = foldr `flip` mempty `flip` f
              $ \mEl acc -> maybe acc (`S.insert` acc) mEl

eval :: Solution
     -> Atom modes polarity terms
     -> Unifier substs
     -> Subseteq (ModedVars polarity terms modes) (Map SubstVarSym0 substs) :~: 'True
     -> S.Set (SomeUnifier (KeepVars (SubstTerms terms substs)))
eval solution atom@(Atom pred@(Predicate _ modes) polarity terms) unifier prf =
  case polarity of
    SPositive -> findUnifiers solution atom'
    SNegative | Refl <- lemNegVars terms modes unifier prf ->
      if S.null (findUnifiers solution (Atom pred SPositive terms'))
        then S.singleton (SU SNil Refl)
        else S.empty
  where
  atom'@(Atom _ _ terms') = substAtom atom unifier

step :: Solution -> Clause -> Solution
step solution (Clause head clauseBody rangeRestriction) =
  (`S.map` walkBody clauseBody) $ \(SU unifier Refl) ->
    deriveHead head unifier rangeRestriction
  where
  walkBody :: Body vars -> S.Set (SomeUnifier vars)
  walkBody BEmpty = S.singleton (SU SNil Refl)
  walkBody (BSnoc body atom@(Atom _ _ terms) prf _) = S.unions $
    (`S.map` walkBody body) $ \(SU unifier Refl) ->
      (`S.map` eval solution atom unifier prf) $ \(SU extension Refl) ->
        case sym $ lemConcatHomo (Sing @_ @SubstVarSym0) extension unifier of
          Refl | Refl <- lemSubstOnVars terms unifier ->
            SU (extension %++ unifier) Refl

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

-- Properties

lemNegVars :: polarity ~ 'Negative
            => STerms terms -> SList modes -> Unifier substs
            -> Subseteq (ModedVars polarity terms modes) (Map SubstVarSym0 substs) :~: 'True
            -> KeepVars (SubstTerms terms substs) :~: '[]
lemNegVars terms modes unifier prf =
  case lemModedVarCorresp terms modes of
    Refl -> lemCompleteSubst terms unifier prf

-- Tests

type Pure1 = '[ 'DontCare ]
type Pure2 = '[ 'DontCare, 'DontCare ]

ancestorP, parentP :: Predicate Pure2
ancestorP      = Predicate "ancestor" sing
parentP        = Predicate "parent" sing

nonHulusiDescP :: Predicate Pure1
nonHulusiDescP = Predicate "nonHulusiDescP" sing

atom1Gen :: Predicate Pure1
         -> SPolarity polarity
         -> STerm term
         -> Atom Pure1 polarity '[term]
atom1Gen pred polarity t1 = Atom pred polarity (t1 `SCons` SNil)

atom2Gen :: Predicate Pure2
         -> SPolarity polarity
         -> STerm term -> STerm term'
         -> Atom Pure2 polarity '[term, term']
atom2Gen pred polarity t1 t2 = Atom pred polarity (t1 `SCons` t2 `SCons` SNil)

ancestorA, parentA
  :: SPolarity polarity
  -> STerm term -> STerm term'
  -> Atom Pure2 polarity '[term, term']
ancestorA     = atom2Gen ancestorP
parentA       = atom2Gen parentP

nonHulusiDescA :: SPolarity polarity -> STerm term -> Atom Pure1 polarity '[term]
nonHulusiDescA = atom1Gen nonHulusiDescP

tuple1Gen :: Predicate Pure1 -> SSymbol sym -> Tuple
tuple1Gen pred s =
  Tuple (Atom pred SPositive (STLit (SLit s) `SCons` SNil)) Refl

tuple2Gen :: Predicate Pure2 -> SSymbol sym1 -> SSymbol sym2 -> Tuple
tuple2Gen pred s1 s2 = Tuple
  (Atom pred SPositive (STLit (SLit s1) `SCons` STLit (SLit s2) `SCons` SNil))
  Refl

ancestorT, parentT :: SSymbol sym1 -> SSymbol sym2 -> Tuple
ancestorT      = tuple2Gen ancestorP
parentT        = tuple2Gen parentP

nonHulusiDescT :: SSymbol sym1 -> Tuple
nonHulusiDescT = tuple1Gen nonHulusiDescP

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

ancestorExpected :: Solution
ancestorExpected = input <> S.fromList
  [ ancestorT (sing @"Nilufer") (sing @"Mistral")
  , ancestorT (sing @"Laurent") (sing @"Mistral")
  , ancestorT (sing @"Hulusi") (sing @"Emir")
  , ancestorT (sing @"Nazli") (sing @"Emir")
  , ancestorT (sing @"Orhan") (sing @"Hulusi")
  , ancestorT (sing @"Orhan") (sing @"Nilufer")
  , ancestorT (sing @"Orhan") (sing @"Emir")
  , ancestorT (sing @"Orhan") (sing @"Mistral")
  ]

reflexiveProgram :: Program
reflexiveProgram = ancestorProgram ++
  case traverse (uncurry mkClause) clauseCandidates of
    Right clauses -> clauses
    Left err -> error err
  where
  clauseCandidates =
    [ ( SA $ nonHulusiDescA SPositive (STVar (SVar $ sing @"X"))
      , [ SA $ ancestorA SPositive (STVar (SVar $ sing @"T")) (STVar (SVar $ sing @"X"))
        , SA $ ancestorA SNegative (STLit (SLit $ sing @"Hulusi")) (STVar (SVar $ sing @"X"))
        ])
    ]

nonHulusiDescExpected :: Solution
nonHulusiDescExpected = ancestorExpected <> S.fromList
  [ nonHulusiDescT (sing @"Nilufer")
  , nonHulusiDescT (sing @"Hulusi")
  , nonHulusiDescT (sing @"Mistral")
  ]

ancestorTest :: IO ()
ancestorTest =
  if output == ancestorExpected
    then putStrLn "Ancestor runs successfully"
    else do
      putStrLn "Ancestor program failed. Here's the output: "
      print output
  where
  output = evaluator ancestorProgram input

nonHulusiDescTest :: IO ()
nonHulusiDescTest =
  if output == nonHulusiDescExpected
    then putStrLn "Non-Hulusi descendant runs successfully"
    else do
      putStrLn "Non-Hulusi descendant failed. Here's the output: "
      print output
  where
  output = evaluator reflexiveProgram input
