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
{-# LANGUAGE UndecidableInstances #-}

module DataflowSafety where

import Prelude hiding (head, round, pred)

import Control.Monad (forM_, guard)

import qualified Data.Text as T
import           Data.Kind (Type)
import           Data.Maybe (isJust)
import qualified Data.Set as S
import           Data.Type.Equality

import qualified Data.Singletons.Prelude      as SP
import qualified Data.Singletons.Prelude.List as SP
import qualified Data.Singletons.TypeLits     as SP
import qualified Data.Singletons.Decide       as SP
import           Data.Singletons.TH (singletons)

import GHC.TypeLits

--------------------------------------------------------------------------------
-- Generic machinery
--------------------------------------------------------------------------------

data Elem :: [ k ] -> k -> Type where
  Here  ::              Elem (k ': ks) k
  There :: Elem ks k -> Elem (a ': ks) k

data All :: (k -> Type) -> [ k ] -> Type where
  Basic :: All p '[]
  Next  :: p k -> All p ks -> All p (k ': ks)

type AllElem (xs :: [ k ]) (ys :: [ k ]) = All (Elem ys) xs

-- ## Term

data Term = Var Symbol | Sym Symbol

data instance SP.Sing (x :: Term) where
  SVar :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Var sym)
  SSym :: KnownSymbol sym => SP.SSymbol sym -> SP.Sing ('Sym sym)

type STerm (x :: Term) = SP.Sing x

data Terms (n :: Nat) (terms :: [ Term ]) =
  Terms (SP.SList terms) (SP.Length terms :~: n)

type VarList (vars :: [ Symbol ]) = SP.SList vars

-- ## Predicate

$(singletons [d|
  data Mode = MPlus | MDontCare
  |])

type Modes (modes :: [ Mode ]) = SP.SList modes

data Predicate (n :: Nat) (modes :: [ Mode ]) =
  Predicate String (Modes modes) (SP.SNat n)

data SomePredicate (n :: Nat) = forall modes.
  KnownNat n => SP (Predicate n modes)

-- ## Atom

data Atom :: [ Symbol ] -> [ Symbol ] -> Type where
  Atom :: Predicate n modes
       -> Terms n terms
       -> Atom (ModedVars modes terms) (Vars terms)

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
            -> AllElem modedVars bodyVars
            -- | All body variables
            -> VarList (atomVars SP.++ bodyVars)
            -> Body (atomVars SP.++ bodyVars)

data SomeBody = forall bodyVars. SB (Body bodyVars)

-- ## Clause

data Clause :: Type where
  Clause :: Head headVars
         -> Body bodyVars
         -- | Range restriction
         -> AllElem headVars bodyVars
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
mkBody (SA atom@(Atom predicate terms) : atoms) = do
  let modedVarList = modedVars predicate terms
  let atomVarList = vars atom
  SB body <- mkBody atoms
  proof <- decWellModedness modedVarList body
  pure $ SB $ SnocBody body atom proof (atomVarList SP.%++ vars body)

mkHead :: SomeAtom -> Maybe SomeHead
mkHead (SA atom@(Atom predicate terms)) =
  case decEmpty (modedVars predicate terms) of
    Just Refl -> Just $ SH atom
    Nothing   -> Nothing

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

class HasVars f where
  vars :: f vars -> VarList vars

instance HasVars (Atom modedVars) where
  vars (Atom _ termList) = keepVars termList

instance HasVars Body where
  vars EmptyBody                 = SP.SNil
  vars (SnocBody _ _ _ bodyVars) = bodyVars

modedVars :: Predicate n modes
          -> Terms n terms
          -> VarList (ModedVars modes terms)
modedVars (Predicate _ modeList _) (Terms terms Refl) = go modeList terms
  where
  go :: Modes modes -> SP.SList terms -> VarList (ModedVars modes terms)
  go SP.SNil                    SP.SNil                = SP.SNil
  go (SMDontCare `SP.SCons` ms) (_      `SP.SCons` ts) =              go ms ts
  go (_          `SP.SCons` ms) (SSym{} `SP.SCons` ts) =              go ms ts
  go (SMPlus     `SP.SCons` ms) (SVar v `SP.SCons` ts) = v `SP.SCons` go ms ts
  go _ _ = error "Mode and term list size mismatch"

keepVars :: Terms n terms -> VarList (Vars terms)
keepVars (Terms ts _) = go ts
  where
  go :: SP.SList terms -> VarList (Vars terms)
  go SP.SNil                   = SP.SNil
  go (SVar v `SP.SCons` terms) = v `SP.SCons` go terms
  go (SSym{} `SP.SCons` terms) =              go terms

type family Vars (terms :: [ Term ]) :: [ Symbol ] where
  Vars '[]                 = '[]
  Vars ('Var var ': terms) = var ': Vars terms
  Vars ('Sym sym ': terms) = Vars terms

type family ModedVars (modes :: [ Mode ]) (terms :: [ Term ]) :: [ Symbol ] where
  ModedVars '[]                '[]              =        '[]
  ModedVars ('MDontCare ': ms) (_ ': ts)        =        ModedVars ms ts
  ModedVars (_          ': ms) ('Sym _   ': ts) =        ModedVars ms ts
  ModedVars ('MPlus     ': ms) ('Var var ': ts) = var ': ModedVars ms ts
  ModedVars _ _ = TypeError ('Text "Modes and terms are not of equal length.")

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

fromDecision :: SP.Decision k -> Maybe k
fromDecision (SP.Proved prf) = Just prf
fromDecision _               = Nothing

decElem :: forall (x :: k) (xs :: [ k ])
         . SP.SDecide k
        => SP.Sing x -> SP.SList xs -> Maybe (Elem xs x)
decElem _ SP.SNil = Nothing
decElem x (y `SP.SCons` ys) =
  case x SP.%~ y of
    SP.Proved Refl -> Just Here
    _              -> There <$> decElem x ys

decAllElem :: forall (xs :: [ k ]) (ys :: [ k ])
            . SP.SDecide k
           => SP.SList xs -> SP.SList ys -> Maybe (AllElem xs ys)
decAllElem SP.SNil           _  = Just Basic
decAllElem (x `SP.SCons` xs) ys = Next <$> decElem x ys <*> decAllElem xs ys

decEmpty :: forall (xs :: [ k ])
          . SP.SDecide k
         => SP.SList xs -> Maybe (xs :~: '[])
decEmpty xs = fromDecision $ xs SP.%~ SP.SNil

decRangeRestriction :: Head headVars
                    -> Body bodyVars
                    -> Maybe (AllElem headVars bodyVars)
decRangeRestriction atom = \case
  EmptyBody -> do
    Refl <- decEmpty $ vars atom
    pure Basic
  SnocBody _ _ _ bodyVars -> decAllElem (vars atom) bodyVars

decWellModedness :: VarList modedVars
                 -> Body bodyVars
                 -> Maybe (AllElem modedVars bodyVars)
decWellModedness modedAtomVars body =
  case body of
    EmptyBody | Refl <- lemListRightId (vars body) -> do
      Refl <- decEmpty modedAtomVars
      pure Basic
    SnocBody{} -> decAllElem modedAtomVars (vars body)

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

lemListRightId :: SP.SList xs -> xs SP.++ '[] :~: xs
lemListRightId SP.SNil                                       = Refl
lemListRightId (_ `SP.SCons` xs) | Refl <- lemListRightId xs = Refl

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

data Substitution     = Substitution Symbol
data SubstitutionTerm = SubstitutionTerm T.Text T.Text

data instance SP.Sing :: Substitution -> Type where
  SSubstitution :: SP.SSymbol var -> T.Text
                -> SP.Sing ('Substitution var)

type SSubstitution (x :: Substitution) = SP.Sing x

instance SP.SingKind Substitution where
  type Demote Substitution = SubstitutionTerm
  fromSing (SSubstitution var symbol) = SubstitutionTerm (SP.fromSing var) symbol
  toSing (SubstitutionTerm var symbol) = case SP.toSing var of
               SP.SomeSing var' -> SP.SomeSing (SSubstitution var' symbol)

type Unifier (substs :: [ Substitution ]) = SP.SList substs

type family Map (f :: k -> l) (xs :: [ k ]) :: [ l ] where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type UnifierVars (terms :: [ Term ]) = Map 'Substitution (Vars terms)

{-
unify :: Terms n terms -> Tuple n -> Maybe (Unifier (UnifierVars terms))
unify = _

findUnifiers :: Atom modedVars vars -> Solution -> S.Set (Unifier vars)
findUnifiers = _

substitute :: Atom modedVars vars -> Unifier vars' ->  Atom modedVars (vars \\ vars')
substitute = _
-}

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

data Tuple n = forall (xs :: [ Symbol ]). T (SP.SList xs) (SP.SNat (SP.Length xs))

data Relation = forall n. KnownNat n => Relation (SomePredicate n) (S.Set (Tuple n))

newtype Solution = Solution [ Relation ] deriving (Eq)

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
someEasy = SA $ Atom easy (Terms (SVar (SP.sing @"X") `SP.SCons` SP.SNil) Refl)

groundP :: Atom '[] '[ "X" ]
groundP = Atom p $ Terms
  (SSym (SP.sing @"Mistral") `SP.SCons` SVar (SP.sing @"X") `SP.SCons` SP.SNil)
  Refl

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom '[ "X" ] '[ "X", "Y" ]
modedP = Atom p $ Terms
  (SVar (SP.sing @"X") `SP.SCons` SVar (SP.sing @"Y") `SP.SCons` SP.SNil)
  Refl

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
