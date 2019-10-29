{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}

module DataflowSafety where

import Prelude hiding (head, round, pred)

import Control.Monad (forM_, guard)

import qualified Data.Text as T
import           Data.Kind (Type)
import           Data.Maybe (isJust, fromJust)
import qualified Data.Set as S
import           Data.Type.Equality

import           Data.Singletons.Set
import qualified Data.Singletons.Prelude      as SP
import qualified Data.Singletons.Prelude.List        as L
import qualified Data.Singletons.Prelude.List.Extras as L
import qualified Data.Singletons.TypeLits     as SP
import qualified Data.Singletons.Decide       as SP
import           Data.Singletons.TH (singletons)

import GHC.TypeLits

-- ## Term

data Term = Var Symbol | Sym Symbol

data instance SP.Sing (x :: Term) where
  SVar :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Var sym)
  SSym :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Sym sym)

type STerm (x :: Term) = SP.Sing x

type Terms (terms :: [ Term ]) = L.SList terms

type Vars (vars :: Set Symbol) = SSet vars

-- ## Predicate

$(singletons [d|
  data Mode = MPlus | MDontCare
  |])

type Modes (modes :: [ Mode ]) = L.SList modes

data Predicate (n :: Nat) (modes :: [ Mode ]) =
  Predicate String (Modes modes) (SP.SNat n)

data SomePredicate (n :: Nat) = forall modes.
  KnownNat n => SP (Predicate n modes)

-- ## Atom

data Atom :: Set Symbol -> Set Symbol -> Type where
  Atom :: KnownNat n
       => Predicate n modes
       -> Terms terms
       -> L.Length terms :~: n
       -> Atom (ModedVars modes terms) (GetVars terms)

data SomeAtom = forall vars modedVars. SA (Atom modedVars vars)

-- ## Head

-- | Clause heads shouldn't have moded predicates, hence they don't have moded
-- variables.
type Head headVars = Atom '[] headVars

data SomeHead = forall vars . SH (Head vars)

-- ## Body

data Body :: [ Symbol ] -> Type where
  EmptyBody :: Body '[]
  SnocBody  :: Body bodyVars
            -> Atom modedVars atomVars
            -- | Well-modedness
            -> Subseteq modedVars bodyVars
            -- | All body variables
            -> Vars (Union atomVars bodyVars)
            -> Body (Union atomVars bodyVars)

data SomeBody = forall bodyVars. SB (Body bodyVars)

-- ## Clause

data Clause :: Type where
  Clause :: Head headVars
         -> Body bodyVars
         -- | Range restriction
         -> Subseteq headVars bodyVars
         -> Clause

-- ## Program

type Program = [ Clause ]

--------------------------------------------------------------------------------
-- Smart constructors: Untyped -> Typed
--------------------------------------------------------------------------------

mkClause :: SomeAtom -> [ SomeAtom ] -> Maybe Clause
mkClause  someHead bodyAtoms = do
  SB body <- mkBody $ reverse bodyAtoms
  SH head <- mkHead someHead
  proof <- decRangeRestriction head body
  pure $ Clause head body proof

mkBody :: [ SomeAtom ] -> Maybe SomeBody
mkBody [] = Just $ SB EmptyBody
mkBody (SA atom@(Atom predicate terms Refl) : atoms) = do
  let modedVarList = modedVars predicate terms
  let atomVarList = vars atom
  SB body <- mkBody atoms
  proof <- decWellModedness modedVarList body
  pure $ SB $ SnocBody body atom proof (atomVarList SP.%++ vars body)

mkHead :: SomeAtom -> Maybe SomeHead
mkHead (SA atom@(Atom predicate terms Refl)) =
  case decEmpty (modedVars predicate terms) of
    Just Refl -> Just $ SH atom
    Nothing   -> Nothing

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

class HasVars f where
  vars :: f vars -> Vars vars

instance HasVars (Atom modedVars) where
  vars (Atom _ termList Refl) = keepVars termList

instance HasVars Body where
  vars EmptyBody                 = SP.SNil
  vars (SnocBody _ _ _ bodyVars) = bodyVars

modedVars :: Predicate n modes -> Terms terms -> Vars (ModedVars modes terms)
modedVars (Predicate _ modeList _) = go modeList
  where
  go :: Modes modes -> Terms terms -> Vars (ModedVars modes terms)
  go SP.SNil                    SP.SNil                = SP.SNil
  go (SMDontCare `SP.SCons` ms) (SVar{} `SP.SCons` ts) =              go ms ts
  go (_          `SP.SCons` ms) (SSym{} `SP.SCons` ts) =              go ms ts
  go (SMPlus     `SP.SCons` ms) (SVar v `SP.SCons` ts) = v `SP.SCons` go ms ts
  go _ _ = error "Mode and term list size mismatch"

keepVars :: Terms terms -> Vars (GetVars terms)
keepVars SP.SNil                   = SP.SNil
keepVars (SVar v `SP.SCons` terms) = v `SP.SCons` keepVars terms
keepVars (SSym{} `SP.SCons` terms) =              keepVars terms

type family GetVars (terms :: [ Term ]) :: Set Symbol where
  GetVars '[]                 = Empty
  GetVars ('Var var ': terms) = Add var (GetVars terms)
  GetVars ('Sym sym ': terms) = GetVars terms

type family ModedVars (modes :: [ Mode ]) (terms :: [ Term ]) :: Set Symbol where
  ModedVars '[]                '[]              = Empty
  ModedVars ('MDontCare ': ms) ('Var _   ': ts) =         ModedVars ms ts
  ModedVars (_          ': ms) ('Sym _   ': ts) =         ModedVars ms ts
  ModedVars ('MPlus     ': ms) ('Var var ': ts) = Add var (ModedVars ms ts)
  ModedVars _ _ = TypeError ('Text "Modes and terms are not of equal length.")

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

decRangeRestriction :: Head headVars
                    -> Body bodyVars
                    -> Maybe (Subseteq headVars bodyVars)
decRangeRestriction atom = \case
  EmptyBody -> do
    Refl <- decEmpty $ vars atom
    pure Basic
  SnocBody _ _ _ bodyVars -> decSubseteq (vars atom) bodyVars

decWellModedness :: Vars modedVars
                 -> Body bodyVars
                 -> Maybe (Subseteq modedVars bodyVars)
decWellModedness modedAtomVars body =
  case body of
    EmptyBody | Refl <- lemSetRightId (vars body) -> do
      Refl <- decEmpty modedAtomVars
      pure Basic
    SnocBody{} -> decSubseteq modedAtomVars (vars body)

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

newtype Substitution  = Subst Symbol
data SubstitutionTerm = SubstTerm T.Text T.Text deriving (Eq, Ord)

type Substs (vars :: Set Symbol) = Map 'Subst vars

type family UnSubsts (substs :: Set Substitution) :: Set Symbol where
  UnSubsts Empty                  = Empty
  UnSubsts ('Subst var ': substs) = Add var (UnSubsts substs)

unifierDom :: SSet substs -> SSet (UnSubsts substs)
unifierDom SEmpty                         = SEmpty
unifierDom (SSubst var _ `SP.SCons` rest) = var :> unifierDom rest

data instance SP.Sing :: Substitution -> Type where
  SSubst :: SP.SSymbol var -> T.Text -> SP.Sing ('Subst var)

type SSubst (x :: Substitution) = SP.Sing x

instance SP.SingKind Substitution where
  type Demote Substitution = SubstitutionTerm
  fromSing (SSubst var symbol) = SubstTerm (SP.fromSing var) symbol
  toSing (SubstTerm var symbol) | SP.SomeSing var' <- SP.toSing var =
     SP.SomeSing (SSubst var' symbol)

type Unifier (substs :: Set Substitution) = SSet substs

instance Eq (Unifier xs) where
  u == v = SP.fromSing u == SP.fromSing v

instance Ord (Unifier xs) where
  u `compare` v = SP.fromSing u `compare` SP.fromSing v

unify :: Atom modedVars pureVars -> Tuple n -> Maybe (Unifier (Substs pureVars))
unify (Atom _ terms Refl) (T syms SP.SNat) = go terms syms
  where
  go :: forall (xs :: [ Term ]) (ys :: [ Symbol ])
      . SP.SList xs -> SP.SList ys -> Maybe (SP.SList (Substs (GetVars xs)))
  go SP.SNil SP.SNil = Just SP.SNil
  go (SSym s' `SP.SCons` ts) (s `SP.SCons` ss)
    | SP.Proved Refl <- s' SP.%~ s = go ts ss
    | otherwise                    = Nothing
  go (SVar v `SP.SCons` ts) (s `SP.SCons` ss) = do
    partialUnifier <- go ts ss
    guard $ consistent v s partialUnifier
    -- The extension to the partial unifier might be redundant if $(v,s)$ is
    -- already in $partialUnifier$, but it simplifies the types.
    pure $ SSubst SP.SSym (SP.fromSing s) `SP.SCons` partialUnifier
  go _ _ = error
    "Impossible. Trying to unify a tuple and terms that do not match in size."

consistent :: SP.SSymbol var -> SP.SSymbol sym -> Unifier substs -> Bool
consistent _ _ SP.SNil = True
consistent svar ssym (SSubst svar' sym' `SP.SCons` substs) =
  case (svar SP.%~ svar', SP.fromSing ssym == sym') of
    (SP.Proved _, False) -> False
    _                    -> consistent svar ssym substs

findUnifiers :: Atom modedVars pureVars -> Solution -> S.Set (Unifier (Substs pureVars))
findUnifiers atom@(Atom predicate _ _) solution =
  case predicate `solLookup` solution of
    Just tuples -> S.map fromJust . S.filter isJust . S.map (unify atom) $ tuples
    Nothing     -> S.empty

data Substituted terms modes substs = forall terms'. Substituted
  (Terms terms')
  (ModedVars modes terms' :~: ModedVars modes terms \\ UnSubsts substs)
  (GetVars terms' :~: GetVars terms \\ UnSubsts substs)
  (L.Length terms :~: L.Length terms')

decElemUnifier :: SP.SSymbol var -> Unifier substs -> Maybe (ElemR (UnSubsts substs) var)
decElemUnifier var unifier = var `decElem` unifierDom unifier

lookupSym :: ElemR (UnSubsts substs) var -> Unifier substs -> T.Text
lookupSym _ SEmpty = error "Unreachable."
lookupSym (L.There el) (SSubst{} `SP.SCons` unifier) = el `lookupSym` unifier
lookupSym L.Here (SSubst _ symbol `SP.SCons` _) = symbol

  {-

substitute :: forall modedVars vars substs
            . Atom modedVars vars
           -> Unifier substs
           -> Atom (modedVars \\ UnSubsts substs) (vars \\ UnSubsts substs)
substitute (Atom predicate@(Predicate _ modes _) terms Refl) unifier
  | Substituted terms' Refl Refl Refl <- go modes terms = Atom predicate terms' Refl
  where
  go :: forall modes terms terms'
      . Modes modes
     -> Terms terms
     -> Substituted terms modes substs
  go SP.SNil SP.SNil = Substituted SP.SNil Refl Refl Refl
  go (SMDontCare `SP.SCons` ms) (t@(SVar var) `SP.SCons` ts)
    | Substituted rest prf1 prf2 Refl <- go ms ts =
      case decElemUnifier var unifier of
        Just elem | SP.SomeSing ssym <- SP.toSing (elem `lookupSym` unifier) ->
          Substituted (SSym ssym `SP.SCons` rest) prf1 prf2 Refl
        Nothing ->
          Substituted (t `SP.SCons` rest) prf1 prf2 Refl
  go (_ `SP.SCons` ms) (t@SSym{} `SP.SCons` ts)
    | Substituted rest prf1 prf2 Refl <- go ms ts = Substituted (t `SP.SCons` rest) prf1 prf2 Refl
  go (SMPlus `SP.SCons` ms) (t@(SVar var) `SP.SCons` ts)
    | Substituted rest prf1 prf2 Refl <- go ms ts = Substituted (t `SP.SCons` rest) prf1 prf2 Refl

  -}

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

data Tuple n = forall (xs :: [ Symbol ]). T (SP.SList xs) (SP.SNat (L.Length xs))

data Relation = forall n. KnownNat n => Relation (SomePredicate n) (S.Set (Tuple n))

newtype Solution = Solution [ Relation ] deriving (Eq)

solLookup :: forall n modes
           . KnownNat n
          => Predicate n modes -> Solution -> Maybe (S.Set (Tuple n))
solLookup pred (Solution rels) = go rels
  where
  sPred :: SomePredicate n
  sPred = SP pred

  go :: [ Relation ] -> Maybe (S.Set (Tuple n))
  go [] = Nothing
  go (Relation pred' tuples : rs)
    | Just Refl <- sPred `testEquality` pred' = Just tuples
    | otherwise = go rs

{-
step :: Solution -> Clause -> Relation
step solution clause = _

round :: Program -> Solution -> Solution
round program solution = mconcat (map (singleton . step solution) program)
                      <> solution

evaluator :: Program -> Solution -> Solution
evaluator program solution =
  if newSolution == solution
    then solution
    else evaluator program newSolution
  where
  newSolution = round program solution
-}

--------------------------------------------------------------------------------
-- Combination
--------------------------------------------------------------------------------

singleton :: Relation -> Solution
singleton = Solution . (:[])

add :: Relation -> Solution -> Solution
add rel (Solution rels) = Solution $ go rel rels
  where
  go :: Relation -> [ Relation ] -> [ Relation ]
  go r [] = [ r ]
  go r1@(Relation (SP (Predicate _ _ ari1)) _)
    (r2@(Relation (SP (Predicate _ _ ari2)) _) : rs) =
    case natVal ari1 `compare` natVal ari2 of
      GT -> r2 : go r1 rs
      EQ -> (r1 <> r2) : rs
      LT -> r1 : r2 : rs

instance Semigroup Solution where
  Solution rels <> solution = foldr add solution rels

instance Monoid Solution where
  mempty = Solution []

instance Semigroup Relation where
  Relation pred tuples <> Relation pred' tuples'
    | Just Refl <- pred `testEquality` pred' = Relation pred $ tuples <> tuples'
    | otherwise = error "Tried to combine relations that does not share a head."

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

instance Eq Relation where
  Relation p1 tuples1 == Relation p2 tuples2
    | Just Refl <- testEquality p1 p2 =
      all (`elem` tuples1) tuples2 &&
      all (`elem` tuples2) tuples1
    | otherwise = False

instance Ord (Tuple n) where
  T xs _ `compare` T ys _ = SP.fromSing xs `compare` SP.fromSing ys

instance Eq (Tuple n) where
  T xs _ == T ys _ = SP.fromSing xs == SP.fromSing ys

instance TestEquality SomePredicate where
  testEquality (SP (Predicate name1 _ arity1))
               (SP (Predicate name2 _ arity2)) = do
    guard (name1 == name2)
    case arity1 SP.%~ arity2 of
      SP.Proved prf -> Just prf
      _ -> Nothing

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

p :: Predicate 2 '[ 'MPlus, 'MDontCare ]
p = Predicate "p" (SMPlus `SP.SCons` SMDontCare `SP.SCons` SP.SNil) SP.SNat

easy :: Predicate 1 '[ 'MDontCare ]
easy = Predicate "easy" (SMDontCare `SP.SCons` SP.SNil)  SP.SNat

someEasy :: SomeAtom
someEasy = SA $ Atom easy (SVar (SP.sing @"X") `SP.SCons` SP.SNil) Refl

groundP :: Atom '[] '[ "X" ]
groundP = Atom p (SSym (SP.sing @"42") `SP.SCons` SVar (SP.sing @"X") `SP.SCons` SP.SNil) Refl

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom '[ "X" ] '[ "X", "Y" ]
modedP = Atom p (SVar (SP.sing @"X") `SP.SCons` SVar (SP.sing @"Y") `SP.SCons` SP.SNil) Refl

someModedP :: SomeAtom
someModedP = SA modedP

tests :: [ ((SomeAtom, [ SomeAtom ]), Bool) ]
tests =
  [ ((someEasy, [ someEasy ]) , True)
  , ((someEasy, [ someModedP ]), False)
  , ((someEasy, [ someGroundP ]), True)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ someEasy, someModedP ]), True)
  , ((someEasy, [ someModedP, someEasy ]), False)
  , ((someEasy, [ someEasy, someGroundP, someModedP ]), True)
  ]

main :: IO ()
main = forM_ (zip tests [(1 :: Int)..]) runTestCase
  where
  runTestCase ((testCase, expectation), ix) =
    putStrLn $ if isJust (uncurry mkClause testCase) == expectation
      then "Test passed."
      else "Test #" <> show ix <> " failed."
