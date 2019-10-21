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
  Atom :: Predicate modes
       -> TermList terms
       -> Atom (ModedVars modes terms) (Vars terms)

data SomeAtom = forall vars modedVars. SA (Atom modedVars vars)

type family ModedVars (modes :: [ Mode ]) (terms :: [ Term ]) :: [ Var ] where
  ModedVars '[]                   '[]                       = '[]
  ModedVars ('MDontCare ': modes) (_ ': terms)              = ModedVars modes terms
  ModedVars (_          ': modes) ('( 'TLit, _)   ': terms) = ModedVars modes terms
  ModedVars ('MPlus     ': modes) ('( 'TVar, var) ': terms) = var ': ModedVars modes terms
  ModedVars _ _ = TypeError (Text "Modes and terms are not of equal length.")

-- ## Predicate

data Predicate (modes :: [ Mode ]) = Predicate String (ModeList modes)

type ModeList (modes :: [ Mode ]) = IxList '[] (:) SMode modes

data Mode = MPlus | MDontCare

data SMode :: Mode -> Type where
  SMPlus     :: SMode MPlus
  SMDontCare :: SMode MDontCare

-- ## Term

type Var = Symbol

data TermTag = TVar | TLit

type Term = (TermTag, Symbol)

data STerm :: Term -> Type where
  STVar :: Proxy sym -> STerm '(TVar, sym)
  STLit :: Proxy sym -> STerm '(TLit, sym)

type TermList (terms :: [ Term ]) = IxList '[] (:) STerm terms

type family Vars (terms :: [ Term ]) :: [ Var ] where
  Vars '[]                       = '[]
  Vars ('( 'TVar, sym) ': terms) = sym ': Vars terms
  Vars ('( 'TLit, _)   ': terms) = Vars terms

type VarList (vars :: [ Var ]) = IxList '[] (:) Proxy vars

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
  vars EmptyBody                 = INil
  vars (SnocBody _ _ _ bodyVars) = bodyVars

modedVars :: Predicate modes -> TermList terms -> VarList (ModedVars modes terms)
modedVars (Predicate _ modeList) = go modeList
  where
  go :: ModeList modes -> TermList terms -> VarList (ModedVars modes terms)
  go INil                     INil                    = INil
  go (SMDontCare :> modeList) (_ :> termList)         = go modeList termList
  go (_ :> modeList)          (STLit{}   :> termList) = go modeList termList
  go (SMPlus :> modeList)     (STVar var :> termList) = var :> go modeList termList
  go _ _ = error "Mode and term list size mismatch"

keepVars :: TermList terms -> VarList (Vars terms)
keepVars INil               = INil
keepVars (STVar v :> terms) = v :> keepVars terms
keepVars (STLit{} :> terms) = keepVars terms

--------------------------------------------------------------------------------
-- Generic machinery
--------------------------------------------------------------------------------

type family (xs :: [ k ]) :++: (ys :: [ k ]) :: [ k ] where
  '[]       :++: ys = ys
  (x ': xs) :++: ys = x ': (xs :++: ys)

infixr 6 :>

data IxList :: b -> (a -> b -> b) -> (a -> Type) -> b -> Type where
  INil ::                                                IxList e f c e
  (:>) :: IxListConstraint a => c a -> IxList e f c b -> IxList e f c (f a b)

class Trivial a

instance Trivial a

type family IxListConstraint (a :: k) :: Constraint where
  IxListConstraint (sym :: Symbol)        = KnownSymbol sym
  IxListConstraint ('(term, sym) :: Term) = KnownSymbol sym
  IxListConstraint a                      = Trivial a

append :: IxList '[] (:) c m
       -> IxList '[] (:) c n
       -> IxList '[] (:) c (m :++: n)
append INil ys = ys
append (x :> xs) ys = x :> append xs ys

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
decElem el INil = Nothing
decElem var (var' :> els) =
  case sameSymbol var var' of
    Just Refl -> Just Here
    Nothing   ->
      case decElem var els of
        Just elemProof -> Just $ There elemProof
        Nothing        -> Nothing

decAllElem :: VarList vars -> VarList vars' -> Maybe (AllElem vars vars')
decAllElem INil ys      = Just Basic
decAllElem (x :> xs) ys =
  case (decElem x ys, decAllElem xs ys) of
    (Just elem, Just allElem) -> Just $ Next elem allElem
    _ -> Nothing

decEmpty :: IxList '[] f a xs -> Maybe (xs :~: '[])
decEmpty INil = Just Refl
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

lemEmptyRight :: IxList '[] (:) p xs -> xs :++: '[] :~: xs
lemEmptyRight INil                                 = Refl
lemEmptyRight (x :> xs) | Refl <- lemEmptyRight xs = Refl

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

p :: Predicate '[ 'MPlus, 'MDontCare ]
p = Predicate "p" (SMPlus :> SMDontCare :> INil)

easy :: Predicate '[ 'MDontCare ]
easy = Predicate "easy" (SMDontCare :> INil)

someEasy = SA $ Atom easy (STVar (Proxy @"X") :> INil)

groundP :: Atom '[] '[ "X" ]
groundP = Atom p (STLit (Proxy @"Mistral") :> STVar (Proxy @"X") :> INil)

{- We can't even construct the following because the type signature says no
    moded vars.

groundP :: Atom '[] '[]
groundP = Atom p (STVar (Proxy @"Mistral") :> STLit (Proxy @"Contrastin") :> INil)
-}

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom '[ "X" ] '[ "X", "Y" ]
modedP = Atom p (STVar (Proxy @"X") :> STVar (Proxy @"Y") :> INil)

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
  forM_ (zip tests [1..]) $ \((testCase, expectation), ix) ->
    putStrLn $ if isJust (uncurry mkClause testCase) == expectation
      then "Test passed."
      else "Test #" <> show ix <> " failed."
