{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}

module DataflowSafety where

import Prelude hiding (head)

import Control.Monad (forM_)

import Data.Kind
import Data.Maybe (isJust)
import Data.Proxy
import Data.Void
import Data.Type.Equality

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
       -> TermList n terms
       -> Atom (ModedVars modes terms) (Vars terms)

data SomeAtom = forall vars modedVars. SA (Atom modedVars vars)

-- ## Predicate

data Predicate (n :: Nat) (modes :: [ Mode ]) =
  Predicate String (Proxy n) (ModeList n modes)

type ModeList (n :: Nat) (modes :: [ Mode ]) = HVect SMode n modes

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

type TermList (n :: Nat) (terms :: [ Term ]) = HVect STerm n terms
type VarList  (vars  :: [ Var ])  = HList Proxy vars

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
          -> TermList  n terms
          -> VarList (ModedVars modes terms)
modedVars (Predicate _ _ modeList) = go modeList
  where
  go :: ModeList n modes -> TermList n terms -> VarList (ModedVars modes terms)
  go HVNil               HVNil              = HNil
  go (SMDontCare :=> ms) (_         :=> ts) =        go ms ts
  go (_          :=> ms) (STLit{}   :=> ts) =        go ms ts
  go (SMPlus     :=> ms) (STVar var :=> ts) = var :> go ms ts
  go _ _ = error "Mode and term list size mismatch"

keepVars :: TermList n terms -> VarList (Vars terms)
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

infixr 5 :=>

data HVect :: (a -> Type) -> Nat -> [ a ] -> Type where
  HVNil  :: HVect c 0 '[]
  (:=>)  :: HListConstraint a => c a -> HVect c n as -> HVect c (1 + n) (a ': as)

class Trivial a

instance Trivial a

type family HListConstraint (a :: k) :: Constraint where
  HListConstraint (sym :: Symbol)        = KnownSymbol sym
  HListConstraint ('(term, sym) :: Term) = KnownSymbol sym
  HListConstraint a                      = Trivial a

append :: HList c m -> HList c n -> HList c (m :++: n)
HNil       `append` ys = ys
(x :> xs) `append` ys = x :> xs `append` ys

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
main =
  forM_ (zip tests [(1 :: Int)..]) $ \((testCase, expectation), ix) ->
    putStrLn $ if isJust (uncurry mkClause testCase) == expectation
      then "Test passed."
      else "Test #" <> show ix <> " failed."
