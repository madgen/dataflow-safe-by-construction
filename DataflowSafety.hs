{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module DataflowSafety where

import Prelude hiding (head, round, pred)

import Control.Monad (forM_, guard)

import qualified Data.Text as T
import           Data.Kind (Type)
import           Data.Maybe (isJust, fromJust)
import qualified Data.Set as S
import           Data.Type.Equality
import           Data.Void (absurd)

import           Data.Singletons.Set
import qualified Data.Singletons.Prelude      as SP
import qualified Data.Singletons.Prelude.List        as L
import qualified Data.Singletons.Prelude.List.Extras as L
import qualified Data.Singletons.TypeLits     as SP
import qualified Data.Singletons.Decide       as SP
import           Data.Singletons.TH

import GHC.TypeLits

-- ## Term

data Term = Var Symbol | Sym Symbol

data instance SP.Sing (x :: Term) where
  SVar :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Var sym)
  SSym :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Sym sym)

type STerm (x :: Term) = SP.Sing x

type Terms (terms :: [ Term ]) = L.SList terms

type Vars (vars :: [ Symbol ]) = L.SList vars

-- ## Predicate

$(singletons [d|
  data Mode = MPlus | MDontCare deriving (Eq)
  |])

type Modes (modes :: [ Mode ]) = L.SList modes

data Predicate (n :: Nat) (modes :: [ Mode ]) =
  Predicate String (Modes modes) (SP.SNat n)

data SomePredicate (n :: Nat) = forall modes.
  KnownNat n => SP (Predicate n modes)

-- ## Atom

data Atom :: Set Term -> Set Mode -> Type where
  Atom :: KnownNat n
       => Predicate n modes
       -> Terms terms
       -> L.Length terms :~: n
       -> Atom terms modes

data SomeAtom = forall terms modes. SA (Atom terms modes)

-- ## Head

-- | Clause heads shouldn't have moded predicates, hence they don't have moded
-- variables.
type Head terms = Atom terms '[]

data SomeHead = forall terms . SH (Head terms)

-- ## Body

data Body :: [ Symbol ] -> Type where
  EmptyBody :: Body '[]
  SnocBody  :: Body bodyVars
            -> Atom terms modes
            -- | Well-modedness
            -> Subseteq (ModedVars terms modes) bodyVars
            -- | All body variables
            -> Vars (Union (Difference (AllVars terms) bodyVars) bodyVars)
            -> Body (Union (Difference (AllVars terms) bodyVars) bodyVars)

data SomeBody = forall bodyVars. SB (Body bodyVars)

-- ## Clause

data Clause :: Type where
  Clause :: Head terms
         -> Body bodyVars
         -- | Range restriction
         -> Subseteq (AllVars terms) bodyVars
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
mkBody (SA atom : atoms) = do
  SB body <- mkBody atoms
  let aVars = allVars atom
  let bVars = bodyVars body
  proof <- decWellModedness (modedVars atom) body
  pure $ SB $ SnocBody body atom proof ((aVars `sDifference` bVars) SP.%++ vars body)

mkHead :: SomeAtom -> Maybe SomeHead
mkHead (SA atom@(Atom (Predicate _ modes _) _ Refl)) =
  case decEmpty modes of
    Just Refl -> Just $ SH atom
    Nothing   -> Nothing

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

class HasVars f where
  vars :: f vars -> Vars vars

instance HasVars Body where
  vars EmptyBody                 = SP.SNil
  vars (SnocBody _ _ _ bodyVars) = bodyVars

type family ModedVars (terms :: [ Term ]) (modes :: [ Mode ]) :: Set Symbol where
  ModedVars '[]              '[]                = Empty
  ModedVars ('Var _   ': ts) ('MDontCare ': ms) =         ModedVars ts ms
  ModedVars ('Sym _   ': ts) ( _         ': ms) =         ModedVars ts ms
  ModedVars ('Var var ': ts) ('MPlus     ': ms) = Add var (ModedVars ts ms)
  ModedVars _ _ = TypeError ('Text "Modes and terms are not of equal length.")

modedVars :: Atom terms modes -> Vars (ModedVars terms modes)
modedVars (Atom (Predicate _ modes _) terms _) = go terms modes
  where
  go :: Terms terms -> Modes modes -> Vars (ModedVars terms modes)
  go SP.SNil                SP.SNil                    = SP.SNil
  go (SVar{} `SP.SCons` ts) (SMDontCare `SP.SCons` ms) =              go ts ms
  go (SSym{} `SP.SCons` ts) (_          `SP.SCons` ms) =              go ts ms
  go (SVar v `SP.SCons` ts) (SMPlus     `SP.SCons` ms) = v `SP.SCons` go ts ms
  go _ _ = error "Mode and term list size mismatch"

type family AllVars (terms :: [ Term ]) :: Set Symbol where
  AllVars '[]                 = '[]
  AllVars ('Var var ': terms) = var ': (AllVars terms)
  AllVars ('Sym sym ': terms) = AllVars terms

allVars :: Atom terms modes -> Vars (AllVars terms)
allVars (Atom _ terms _) = go terms
  where
  go :: Terms terms -> Vars (AllVars terms)
  go SP.SNil                   = SP.SNil
  go (SVar v `SP.SCons` ts) = v `SP.SCons` go ts
  go (SSym{} `SP.SCons` ts) =              go ts

type PureVars (terms :: [ Term ]) (modes :: [ Mode ]) =
  Difference (AllVars terms) (ModedVars terms modes)

pureVars :: Atom terms modes -> Vars (PureVars terms modes)
pureVars atom = allVars atom `sDifference` modedVars atom

bodyVars :: Body bodyVars -> Vars bodyVars
bodyVars EmptyBody                = L.SNil
bodyVars (SnocBody _ _ _ allVars) = allVars

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

decRangeRestriction :: Head terms
                    -> Body bodyVars
                    -> Maybe (Subseteq (AllVars terms) bodyVars)
decRangeRestriction atom = \case
  EmptyBody -> do
    Refl <- decEmpty $ allVars atom
    pure L.Basic
  SnocBody _ _ _ bodyVars -> decSubseteq (allVars atom) bodyVars

decWellModedness :: Vars modedVars
                 -> Body bodyVars
                 -> Maybe (Subseteq modedVars bodyVars)
decWellModedness modedAtomVars body =
  case body of
    EmptyBody | Refl <- lemSetRightId (vars body) -> do
      Refl <- decEmpty modedAtomVars
      pure L.Basic
    SnocBody{} -> decSubseteq modedAtomVars (vars body)

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------
  {-
data SomeSym = forall sym. KnownSymbol sym => SomeSym (SP.SSymbol sym)

type Unifier vars = (L.SList vars, [ SomeSym ])

instance Eq SomeSym where
  SomeSym s == SomeSym s' = SP.fromSing s == SP.fromSing s'

instance Ord SomeSym where
  SomeSym s `compare` SomeSym s' = SP.fromSing s `compare` SP.fromSing s'

instance {-# OVERLAPPING #-} Eq (Unifier (vars :: [ Symbol ])) where
  (vs,ss) == (vs',ss') = SP.fromSing vs == SP.fromSing vs' && ss == ss'

instance {-# OVERLAPPING #-} Ord (Unifier (vars :: [ Symbol ])) where
  (vs,ss) `compare` (vs',ss') = (SP.fromSing vs,ss) `compare` (SP.fromSing vs',ss')

unify :: Atom terms modes -> Tuple -> Maybe (Unifier (AllVars terms))
unify atom@(Atom _ terms Refl) tuple = go terms tuple
  where
  go :: forall (terms :: [ Term ])
      . L.SList terms -> [ SomeSym ] -> Maybe (Unifier (AllVars terms))
  go L.SNil [] = Just (L.SNil, [])
  go (SSym s' `SP.SCons` ts) (SomeSym s : ss)
    | SP.Proved Refl <- s' SP.%~ s = go ts ss
    | otherwise                    = Nothing
  go (SVar v `SP.SCons` ts) (s : ss) = do
    unifier@(vs', ss') <- go ts ss
    guard $ consistent v s unifier
    -- The extension to the partial unifier might be redundant if $(v,s)$ is
    -- already in $partialUnifier$, but it simplifies the types.
    pure $ (SP.SSym `SP.SCons` vs', s : ss')
  go _ _ = error
    "Impossible. Trying to unify a tuple and terms that do not match in size."

consistent :: SP.SSymbol var -> SomeSym -> (Vars vars, [ SomeSym ]) -> Bool
consistent _ _ (SP.SNil, []) = True
consistent sv s'@(SomeSym s) (svar' `SP.SCons` svars, SomeSym ssym' : syms) =
  case (sv SP.%~ svar', s SP.%~ ssym') of
    (SP.Proved _, SP.Disproved _) -> False
    _                             -> consistent sv s' (svars, syms)
consistent _ _ _ = error "Unifier has uneven number of vars and symbols"

findUnifiers :: Atom terms modes -> Solution -> S.Set (Unifier (AllVars terms))
findUnifiers atom@(Atom predicate _ _) solution =
  case predicate `solLookup` solution of
    Just tuples -> S.map fromJust . S.filter isJust . S.map (unify atom) $ tuples
    Nothing     -> S.empty

decElemUnifier :: SP.SSymbol var -> Unifier vars -> Maybe (ElemR vars var)
decElemUnifier var unifier = var `decElem` fst unifier

lookupSym :: ElemR vars var -> Unifier vars -> SomeSym
lookupSym _            (L.SNil,[])                     = error "Unreachable."
lookupSym (L.There el) (_ `SP.SCons` vs, _      : ss ) = el `lookupSym` (vs, ss)
lookupSym L.Here       (_              , symbol : _  ) = symbol
lookupSym _ _ = error "Unifier has uneven number of vars and symbols"

  -}

  {-
data SubstitutedAtom terms modes vars = forall terms'.
  SubstAtom (Atom terms' modes)
            (AllVars terms' :~: Difference (AllVars terms) vars)
            (Length terms' :~: Length terms)

data SubstitutedTerms terms vars n = forall terms'.
  SubstTerms (Terms terms')
             (AllVars terms' :~: Difference (AllVars terms) vars)
             (Length terms' :~: n)

substituteVar :: forall n terms vars var
               . SubstitutedTerms terms vars n
              -> (SP.SSymbol var, SomeSym)
              -> SubstitutedTerms terms (var ': vars) n
substituteVar (SubstTerms L.SNil Refl prf') _ = (SubstTerms L.SNil Refl prf')
  {-
substituteVar (SubstTerms (t@(SSym s) `L.SCons` ts) prf Refl) subst =
  case substituteVar (SubstTerms @terms @vars @(n - 1) ts prf Refl) subst of
    SubstTerms ts' prf' Refl -> SubstTerms (t `L.SCons` ts') prf' Refl
  -}
substituteVar (SubstTerms (t `L.SCons` ts) prf Refl :: SubstitutedTerms (t ': ts) vars n) subst@(svar', SomeSym sym') =
  _
  {-
  case t of
    SSym s ->
      case substituteVar (SubstTerms @terms @vars @(n - 1) ts prf Refl) subst of
        SubstTerms ts' prf' Refl -> SubstTerms (t `L.SCons` ts') prf' Refl
    SVar svar ->
      case svar %== svar' of
        STrue ->
          case substituteVar (SubstTerms @terms @vars @(n - 1) ts _ Refl) subst of
            SubstTerms ts' prf' Refl -> SubstTerms (SSym sym' `L.SCons` ts') _ Refl
        SFalse ->
          case substituteVar (SubstTerms @terms @vars @(n - 1) ts _ Refl) subst of
            SubstTerms ts' prf' Refl -> SubstTerms (t `L.SCons` ts') _ Refl
  -}

  {-
data SubstitutedTerms' terms vars = forall terms'.
  SubstTerms' (Terms terms')
              (AllVars terms' :~: Difference (AllVars terms) vars)
              (Length terms' :~: Length terms)

substituteVar' :: forall terms vars var
                . Terms terms
               -> SubstitutedTerms' terms vars
               -> (SP.SSymbol var, SomeSym)
               -> SubstitutedTerms' terms (var ': vars)
substituteVar' L.SNil (SubstTerms' L.SNil Refl Refl) _ = (SubstTerms' L.SNil Refl Refl)
substituteVar' (t `L.SCons` ts) (SubstTerms' (t' `L.SCons` ts') prf Refl) subst@(svar, SomeSym s) =
  _
  case t' of
    SSym _ ->
      case substituteVar' ts (SubstTerms' @_ @vars ts' _ Refl) subst of
        SubstTerms' ts'' prf' Refl -> SubstTerms' (t `L.SCons` ts'') _ Refl
    SVar svar' ->
      case svar %== svar' of
        STrue ->
          case substituteVar' ts (SubstTerms' @_ @vars ts' _ Refl) subst of
            SubstTerms' ts' prf' Refl -> SubstTerms' (SSym s `L.SCons` ts') _ Refl
        SFalse ->
          case substituteVar' ts (SubstTerms' @_ @vars ts' _ Refl) subst of
            SubstTerms' ts' prf' Refl -> SubstTerms' (t `L.SCons` ts') prf' Refl
  -}

substitute :: forall terms terms' modes vars
            . Atom terms modes
           -> Unifier vars
           -> SubstitutedAtom terms modes vars
substitute (Atom predicate terms Refl) unifier =
  case go terms unifier of
    SubstTerms terms' prf Refl -> SubstAtom (Atom predicate terms' Refl) prf Refl
  where
  go :: forall terms vars. Terms terms -> Unifier vars -> SubstitutedTerms terms vars (L.Length terms)
  go ts (L.SNil,[]) = SubstTerms ts Refl Refl
  go ts (svar `L.SCons` svars, s : ss) = substituteVar (go ts (svars, ss)) (svar, s)

extend :: Unifier vars -> Unifier vars' -> Unifier (vars' L.++ vars)
extend (baseVars, baseSyms) (extensionVars, extensionSyms) =
  (extensionVars L.%++ baseVars, extensionSyms ++ baseSyms)

  -}

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

  {-

type Tuple = [ SomeSym ]

data Relation = forall n. KnownNat n => Relation (SomePredicate n) (S.Set Tuple)

newtype Solution = Solution [ Relation ] deriving (Eq)

solLookup :: forall n modes
           . KnownNat n
          => Predicate n modes -> Solution -> Maybe (S.Set Tuple)
solLookup pred (Solution rels) = go rels
  where
  sPred :: SomePredicate n
  sPred = SP pred

  go :: [ Relation ] -> Maybe (S.Set Tuple)
  go [] = Nothing
  go (Relation pred' tuples : rs)
    | Just Refl <- sPred `testEquality` pred' = Just tuples
    | otherwise = go rs

data SubstitutedHead = forall terms. SubstHead (Head terms) (AllVars terms :~: '[])

step :: Solution -> Clause -> Relation
step solution (Clause head@(Atom predicate _ _) body rangeRestriction) =
  Relation (SP predicate) $ (`S.map` walkBody body) $ \unifier ->
    fromHead (deriveHead head unifier rangeRestriction)
  where
  walkBody :: Body vars -> S.Set (Unifier vars)
  walkBody EmptyBody = S.singleton (L.SNil, [])
  walkBody (SnocBody body atom _ _) = S.unions $ (`S.map` walkBody body) $ \unifier ->
    case substitute atom unifier of
      SubstAtom atom' Refl Refl ->
        (`S.map` findUnifiers atom' solution) $ \unifierExtension ->
          extend unifier unifierExtension

  deriveHead :: forall terms terms' vars
              . Head terms -> Unifier vars -> Subseteq (AllVars terms) vars
             -> SubstitutedHead
  deriveHead head unifier subseteq =
    case substitute head unifier of
      SubstAtom head' Refl Refl
        | Refl <- lemEmptyDiff (allVars head) (fst unifier) subseteq ->
          SubstHead head' Refl

  lemEmptyDiff :: L.SList xs -> L.SList ys -> Subseteq xs ys -> Difference xs ys :~: '[]
  lemEmptyDiff _ ys L.Basic | Refl <- lemDiffFromNada ys = Refl
  lemEmptyDiff xs ys (prf `L.Next` prfs) | Refl <- lemDiffStep xs prf = _

  lemDiffStep :: forall x xs ys. L.SList xs -> ElemR ys x -> Difference (x ': xs) ys :~: Difference xs ys
  lemDiffStep = _

  fromHead :: SubstitutedHead -> Tuple
  fromHead (SubstHead (Atom _ terms _) prf) = go terms prf
    where
    go :: Terms terms -> AllVars terms :~: '[] -> Tuple
    go L.SNil _ = []
    go (SSym s `L.SCons` ss) Refl | tuple <- go ss Refl = SomeSym s : tuple
    go (SVar _ `L.SCons` _) prf = absurd (absurdList prf)

  absurdList :: (x ': xs) :~: '[] -> Void
  absurdList Refl = error "From nothing comes nothing"

lemDiffFromNada :: L.SList xs -> Difference '[] xs :~: '[]
lemDiffFromNada L.SNil = Refl
lemDiffFromNada (_ `L.SCons` xs) | Refl <- lemDiffFromNada xs = Refl

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

instance TestEquality SomePredicate where
  testEquality (SP (Predicate name1 _ arity1))
               (SP (Predicate name2 _ arity2)) = do
    guard (name1 == name2)
    case arity1 SP.%~ arity2 of
      SP.Proved prf -> Just prf
      _ -> Nothing

  -}

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

type PMode = '[ 'MPlus, 'MDontCare ]

p :: Predicate 2 PMode
p = Predicate "p" (SMPlus `SP.SCons` SMDontCare `SP.SCons` SP.SNil) SP.SNat

easy :: Predicate 1 '[ 'MDontCare ]
easy = Predicate "easy" (SMDontCare `SP.SCons` SP.SNil)  SP.SNat

someEasy :: SomeAtom
someEasy = SA $ Atom easy (SVar (SP.sing @"X") `SP.SCons` SP.SNil) Refl

groundP :: Atom '[ 'Sym "42", 'Var "X" ] PMode
groundP = Atom p (SSym (SP.sing @"42") `SP.SCons` SVar (SP.sing @"X") `SP.SCons` SP.SNil) Refl

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom '[ 'Var "X", 'Var "Y" ] PMode
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
