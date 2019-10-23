{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module DataflowSafety where

import Prelude hiding (head, round, pred)

import Control.Monad (forM_, guard)

import           Data.Kind (Type, Constraint)
import           Data.Maybe (isJust)
import           Data.Proxy (Proxy(..))
import qualified Data.Set as S
import           Data.Type.Equality
import           Data.Void

import GHC.TypeLits

-- ## Program

type Program = [ Clause ]

-- ## Clause

data Clause :: Type where
  Clause :: Head headVars
         -> Body bodyVars
         -- | Range restriction
         -> AllElem headVars bodyVars
         -> Clause

-- ## Head

-- | Clause heads shouldn't have moded predicates, hence they don't have moded
-- variables.
type Head headVars = Atom '[] headVars

data SomeHead = forall vars . SH (Head vars)

-- ## Body

data Body :: [ Var ] -> Type where
  EmptyBody :: Body '[]
  SnocBody  :: Body bodyVars
            -> Atom modedVars atomVars
            -- | Well-modedness
            -> AllElem modedVars bodyVars
            -- | All body variables
            -> VarList (atomVars :++: bodyVars)
            -> Body (atomVars :++: bodyVars)

data SomeBody = forall bodyVars. SB (Body bodyVars)

-- ## Atom

data Atom :: [ Var ] -> [ Var ] -> Type where
  Atom :: Predicate n modes
       -> Terms n terms
       -> Atom (ModedVars modes terms) (Vars terms)

data SomeAtom = forall vars modedVars. SA (Atom modedVars vars)

-- ## Predicate

data Predicate (n :: Nat) (modes :: [ Mode ]) =
  Predicate String (Proxy n) (Modes n modes)

data SomePredicate (n :: Nat) = forall modes.
  KnownNat n => SP (Predicate n modes)

type Modes (n :: Nat) (modes :: [ Mode ]) = HVect n SMode modes

data Mode = MPlus | MDontCare

data SMode :: Mode -> Type where
  SMPlus     :: SMode 'MPlus
  SMDontCare :: SMode 'MDontCare

-- ## Term

type Var = Symbol

data TermTag = TVar | TLit

type Term = (TermTag, Symbol)

data STerm :: Term -> Type where
  STVar :: Proxy sym -> STerm '( 'TVar, sym)
  STLit :: Proxy sym -> STerm '( 'TLit, sym)

type Terms (n :: Nat) (terms :: [ Term ]) = HVect n STerm terms
type SomeTerms n = SomeHVect n STerm

type VarList (vars :: [ Var ]) = HList Proxy vars

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
  pure $ SB $ SnocBody body atom proof (atomVarList `append` vars body)

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
  vars EmptyBody                 = HNil
  vars (SnocBody _ _ _ bodyVars) = bodyVars

modedVars :: Predicate n modes
          -> Terms  n terms
          -> VarList (ModedVars modes terms)
modedVars (Predicate _ _ modeList) = go modeList
  where
  go :: Modes n modes -> Terms n terms -> VarList (ModedVars modes terms)
  go HVNil               HVNil              = HNil
  go (SMDontCare :=> ms) (_         :=> ts) =        go ms ts
  go (_          :=> ms) (STLit{}   :=> ts) =        go ms ts
  go (SMPlus     :=> ms) (STVar var :=> ts) = var :> go ms ts
  go _ _ = error "Mode and term list size mismatch"

keepVars :: Terms n terms -> VarList (Vars terms)
keepVars HVNil               = HNil
keepVars (STVar v :=> terms) = v :> keepVars terms
keepVars (STLit{} :=> terms) = keepVars terms

type family Vars (terms :: [ Term ]) :: [ Var ] where
  Vars '[]                       = '[]
  Vars ('( 'TVar, sym) ': terms) = sym ': Vars terms
  Vars ('( 'TLit, _)   ': terms) = Vars terms

type family ModedVars (modes :: [ Mode ]) (terms :: [ Term ]) :: [ Var ] where
  ModedVars '[]                '[]                    =        '[]
  ModedVars ('MDontCare ': ms) (_ ': ts)              =        ModedVars ms ts
  ModedVars (_          ': ms) ('( 'TLit, _)   ': ts) =        ModedVars ms ts
  ModedVars ('MPlus     ': ms) ('( 'TVar, var) ': ts) = var ': ModedVars ms ts
  ModedVars _ _ = TypeError ('Text "Modes and terms are not of equal length.")

--------------------------------------------------------------------------------
-- Generic machinery
--------------------------------------------------------------------------------

type family (xs :: [ k ]) :++: (ys :: [ k ]) :: [ k ] where
  '[]       :++: ys = ys
  (x ': xs) :++: ys = x ': (xs :++: ys)

infixr 5 :>
data HList :: (a -> Type) -> [ a ] -> Type where
  HNil :: HList c '[]
  (:>) :: HListConstraint a => c a -> HList c as -> HList c (a ': as)

data SomeHList p = forall xs. SHL (HList p xs)

infixr 5 :=>
data HVect :: Nat -> (a -> Type) -> [ a ] -> Type where
  HVNil  :: HVect 0 c '[]
  (:=>)  :: HListConstraint a => c a -> HVect n c as -> HVect (1 + n) c (a ': as)

data SomeHVect n p = forall xs. SHV (HVect n p xs)

class Trivial a

instance Trivial a

type family HListConstraint (a :: k) :: Constraint where
  HListConstraint (sym :: Symbol)        = KnownSymbol sym
  HListConstraint ('(term, sym) :: Term) = KnownSymbol sym
  HListConstraint a                      = Trivial a

append :: HList c m -> HList c n -> HList c (m :++: n)
HNil      `append` ys = ys
(x :> xs) `append` ys = x :> (xs `append` ys)

data Dec :: Type -> Type where
  Yes :: k           -> Dec k
  No  :: (k -> Void) -> Dec k

data Elem :: [ k ] -> k -> Type where
  Here  ::              Elem (k ': ks) k
  There :: Elem ks k -> Elem (a ': ks) k

data All :: (k -> Type) -> [ k ] -> Type where
  Basic :: All p '[]
  Next  :: p k -> All p ks -> All p (k ': ks)

type AllElem xs ys = All (Elem ys) xs

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

decElem :: forall var vars. KnownSymbol var
        => Proxy var -> VarList vars -> Maybe (Elem vars var)
decElem _ HNil = Nothing
decElem var (var' :> els) =
  case sameSymbol var var' of
    Just Refl -> Just Here
    Nothing   ->
      case decElem var els of
        Just elemProof -> Just $ There elemProof
        Nothing        -> Nothing

decAllElem :: VarList vars -> VarList vars' -> Maybe (AllElem vars vars')
decAllElem HNil _       = Just Basic
decAllElem (x :> xs) ys =
  case (decElem x ys, decAllElem xs ys) of
    (Just el, Just allElem) -> Just $ Next el allElem
    _ -> Nothing

decEmpty :: HList a xs -> Maybe (xs :~: '[])
decEmpty HNil = Just Refl
decEmpty _    = Nothing

decRangeRestriction :: Head headVars
                    -> Body bodyVars
                    -> Maybe (AllElem headVars bodyVars)
decRangeRestriction atom body =
  case body of
    EmptyBody -> do
      Refl <- decEmpty $ vars atom
      pure Basic
    SnocBody _ _ _ bodyVars -> decAllElem (vars atom) bodyVars

decWellModedness :: VarList modedVars
                 -> Body bodyVars
                 -> Maybe (AllElem modedVars bodyVars)
decWellModedness modedAtomVars body =
  case body of
    EmptyBody | Refl <- lemEmptyRight (vars body) -> do
      Refl <- decEmpty modedAtomVars
      pure Basic
    SnocBody{} -> decAllElem modedAtomVars (vars body)

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

lemEmptyRight :: HList p xs -> xs :++: '[] :~: xs
lemEmptyRight HNil                                 = Refl
lemEmptyRight (_ :> xs) | Refl <- lemEmptyRight xs = Refl

--------------------------------------------------------------------------------
-- Datalog evaluator
--------------------------------------------------------------------------------

data Tuple n = forall (xs :: [ Var ]). T (HVect n Proxy xs)

data Relation = forall n. Relation (SomePredicate n) (S.Set (Tuple n))

newtype Solution = Solution [ Relation ] deriving (Eq)

{-
step :: Solution -> Clause -> Relation
step solution Clause = _

round :: Program -> Solution -> Solution
round program solution = mconcat (map (singleton . step $ solution) program)
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
  go r1@(Relation (SP (Predicate _ ari1 _)) _)
    (r2@(Relation (SP (Predicate _ ari2 _)) _) : rs) =
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
  T HVNil      `compare` T HVNil = EQ
  T (x :=> xs) `compare` T (y :=> ys) =
    case symbolVal x `compare` symbolVal y of
      EQ  -> T xs `compare` T ys
      cmp -> cmp
  _ `compare` _ = error "Impossible strikes once again."

instance Eq (Tuple n) where
  T vec1 == T vec2 = go vec1 vec2
    where
    go :: forall m (xs :: [ Symbol ]) (ys :: [ Symbol ])
        . HVect m Proxy xs -> HVect m Proxy ys -> Bool
    go HVNil      HVNil        = False
    go (v :=> vs) (v' :=> vs') = isJust (sameSymbol v v') && go vs vs'
    go _ _ = error "Impossible for tuple vector not to be equal size"

instance TestEquality SomePredicate where
  testEquality (SP (Predicate name1 arity1 _))
               (SP (Predicate name2 arity2 _)) = do
    guard (name1 == name2)
    sameNat arity1 arity2

instance TestEquality p => TestEquality (HList p) where
  testEquality HNil HNil = Just Refl
  testEquality (x :> xs) (y :> ys) = do
    Refl <- x  `testEquality` y
    Refl <- xs `testEquality` ys
    pure Refl
  testEquality _ _ = Nothing

instance TestEquality p => TestEquality (HVect n p) where
  testEquality HVNil HVNil = Just Refl
  testEquality (x :=> xs) (y :=> ys) = do
    Refl <- x  `testEquality` y
    Refl <- xs `testEquality` ys
    pure Refl
  testEquality _ _     = error "Impossible in hetero vector comparison."

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

p :: Predicate 2 '[ 'MPlus, 'MDontCare ]
p = Predicate "p" Proxy (SMPlus :=> SMDontCare :=> HVNil)

easy :: Predicate 1 '[ 'MDontCare ]
easy = Predicate "easy" Proxy (SMDontCare :=> HVNil)

someEasy :: SomeAtom
someEasy = SA $ Atom easy (STVar (Proxy @"X") :=> HVNil)

groundP :: Atom '[] '[ "X" ]
groundP = Atom p (STLit (Proxy @"Mistral") :=> STVar (Proxy @"X") :=> HVNil)

{- We can't even construct the following because the type signature says no
    moded vars.

groundP :: Atom '[] '[]
groundP = Atom p (STVar (Proxy @"Mistral") :> STLit (Proxy @"Contrastin") :> INil)
-}

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom '[ "X" ] '[ "X", "Y" ]
modedP = Atom p (STVar (Proxy @"X") :=> STVar (Proxy @"Y") :=> HVNil)

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
