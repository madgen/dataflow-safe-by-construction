{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Types where

import Prelude hiding (head, pred)

import Control.Monad (guard, forM_)

import           Data.Kind (Type)
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Head)
import           Data.Singletons.TH
import           Data.Singletons.TypeLits
import qualified Data.Text as T
import           Data.Type.Equality hiding (type (==), sym)

import Set

-- Variable singletons

newtype VariableT = VarT T.Text deriving (Eq, Ord)
newtype Variable  = Var Symbol

data instance Sing (var :: Variable) where
  SVar :: Sing var -> Sing ('Var var)

type SVariable (var :: Variable) = Sing var

instance SingKind Variable where
  type Demote Variable = VariableT
  fromSing (SVar ssym) = VarT $ fromSing ssym
  toSing (VarT text) | SomeSing sym <- toSing text = SomeSing (SVar sym)

instance KnownSymbol var => SingI ('Var var) where
  sing = SVar sing

$(singletonsOnly [d|
  instance Eq Variable where
    Var sym == Var sym' = sym == sym'

  instance Ord Variable where
    Var sym `compare` Var sym' = sym `compare` sym'
  |])

-- Literal singletons

newtype LiteralT = LitT T.Text deriving (Eq, Ord)
newtype Literal  = Lit Symbol

$(genDefunSymbols [''Literal])

type SomeLit = SomeSing Literal

data instance Sing (lit :: Literal) where
  SLit :: Sing lit -> Sing ('Lit lit)

type SLiteral (lit :: Literal) = Sing lit

instance SingKind Literal where
  type Demote Literal = LiteralT
  fromSing (SLit ssym) = LitT $ fromSing ssym
  toSing (LitT text) | SomeSing sym <- toSing text = SomeSing (SLit sym)

instance KnownSymbol var => SingI ('Lit var) where
  sing = SLit sing

$(singletonsOnly [d|
  instance Eq Literal where
    Lit sym == Lit sym' = sym == sym'

  instance Ord Literal where
    Lit sym `compare` Lit sym' = sym `compare` sym'
  |])

-- Term singletons

data TermT = TVarT VariableT | TLitT LiteralT deriving (Eq, Ord)
data Term  = TVar Variable   | TLit Literal

$(genDefunSymbols [''Term])

data instance Sing (term :: Term) where
  STVar :: Sing var -> Sing ('TVar var)
  STLit :: Sing lit -> Sing ('TLit lit)

type STerm (term :: Term) = Sing term

instance SingKind Term where
  type Demote Term = TermT

  fromSing (STLit slit) = TLitT $ fromSing slit
  fromSing (STVar svar) = TVarT $ fromSing svar

  toSing (TLitT lit) | SomeSing slit <- toSing lit = SomeSing (STLit slit)
  toSing (TVarT var) | SomeSing svar <- toSing var = SomeSing (STVar svar)

$(singletonsOnly [d|
  instance Eq Term where
    TVar var == TVar var' = var == var'
    TLit lit == TLit lit' = lit == lit'
    TVar{} == TLit{} = False
    TLit{} == TVar{} = False

  instance Ord Term where
    TVar var `compare` TVar var' = var `compare` var'
    TLit lit `compare` TLit lit' = lit `compare` lit'
    TVar{} `compare` TLit{} = GT
    TLit{} `compare` TVar{} = LT
  |])

-- Collections for vars and terms

type STerms (terms :: [ Term ]) = SList terms
type SVars (vars :: [ Variable ]) = SList vars

$(singletons [d|
  keepVars :: [ Term ] -> [ Variable ]
  keepVars [] = []
  keepVars (TVar var : terms) = var : keepVars terms
  keepVars (TLit{} : terms) = keepVars terms
  |])

-- Modes

$(singletons [d|
  data Mode = Plus | DontCare deriving (Eq)

  modedVars :: [ Term ] -> [ Mode ] -> [ Variable ]
  modedVars [] [] = []
  modedVars (TVar{}   : ts) (DontCare : ms) =       modedVars ts ms
  modedVars (TVar var : ts) (Plus     : ms) = var : modedVars ts ms
  modedVars (TLit{}   : ts) (_        : ms) =       modedVars ts ms
  modedVars _ _ = error "Uneven number of terms and modes"
  |])

type SModes (modes :: [ Mode ]) = SList modes

-- Predicate

data Predicate (modes :: [ Mode ]) = Predicate T.Text (SModes modes)

instance TestEquality Predicate where
  testEquality (Predicate name sModes) (Predicate name' sModes') = do
    guard (name == name')
    case sModes %~ sModes' of
      Proved a     -> Just a
      Disproved _ -> Nothing

-- Atom

data Atom (modes :: [ Mode ]) (terms :: [ Term ]) =
  Atom (Predicate modes) (STerms terms)

data SomeAtom = forall modes terms. SA (Atom modes terms)

data Tuple = forall modes terms. Tuple (Atom modes terms) (KeepVars terms :~: '[])

instance Eq Tuple where
  Tuple (Atom (Predicate name _) sTerms) _ ==
    Tuple (Atom (Predicate name' _) sTerms') _ =
    name == name' && fromSing sTerms == fromSing sTerms'

instance Ord Tuple where
  Tuple (Atom (Predicate name _) terms) _ `compare`
    Tuple (Atom (Predicate name' _) terms') _ =
      (name, fromSing terms) `compare` (name', fromSing terms')

-- Clause

$(singletonsOnly [d|
  isPure :: [ Mode ] -> Bool
  isPure = all (DontCare ==)
  |])

data Head terms = forall modes. Head (Atom modes terms) (IsPure modes :~: 'True)

data SomeHead = forall terms. SH (Head terms)

data Body :: [ Variable ] -> Type where
  BEmpty :: Body '[]
  BSnoc  :: Body bodyVars
         -> Atom modes terms
         -- | Well-modedness
         -> Subseteq (ModedVars terms modes) bodyVars :~: 'True
         -- | All body variables
         -> SVars (Exclude (KeepVars terms) bodyVars ++ bodyVars)
         -> Body  (Exclude (KeepVars terms) bodyVars ++ bodyVars)

data SomeBody = forall vars. SB (Body vars)

sBodyVars :: Body vars -> SVars vars
sBodyVars BEmpty = SNil
sBodyVars (BSnoc _ _ _ sVars) = sVars

data Clause :: Type where
  Clause :: Head terms
         -> Body bodyVars
         -- | Range restriction
         -> Subseteq (KeepVars terms) bodyVars :~: 'True
         -> Clause

-- Program

type Program = [ Clause ]

-- Decision procedures

decRangeRestriction :: Head terms -> Body bodyVars
                    -> Maybe (Subseteq (KeepVars terms) bodyVars :~: 'True)
decRangeRestriction (Head (Atom _ sTerms) Refl) body =
  case sSubseteq (sKeepVars sTerms) (sBodyVars body) of
    STrue  -> Just Refl
    SFalse -> Nothing

decWellModedness :: Atom modes terms -> Body bodyVars
                 -> Maybe (Subseteq (ModedVars terms modes) bodyVars :~: 'True)
decWellModedness (Atom (Predicate _ sModes) sTerms) body =
  case sSubseteq (sModedVars sTerms sModes) (sBodyVars body) of
    STrue  -> Just Refl
    SFalse -> Nothing

decPureAtom :: Atom modes terms -> Maybe (IsPure modes :~: 'True)
decPureAtom (Atom (Predicate _ sModes) _) =
  case sIsPure sModes of
    STrue  -> Just Refl
    SFalse -> Nothing

-- Smart constructors

mkClause :: SomeAtom -> [ SomeAtom ] -> Either String Clause
mkClause  someHead bodyAtoms = do
  SB body <- mkBody $ reverse bodyAtoms
  SH head <- mkHead someHead
  case decRangeRestriction head body of
    Just proof -> pure $ Clause head body proof
    Nothing -> Left "Clause is not range restricted."

mkBody :: [ SomeAtom ] -> Either String SomeBody
mkBody [] = Right $ SB BEmpty
mkBody (SA atom@(Atom _ terms) : atoms) = do
  SB body <- mkBody atoms
  let aVars = sKeepVars terms
  let bVars = sBodyVars body
  case decWellModedness atom body of
    Just proof -> do
      let newBVars = (aVars `sExclude` bVars) %++ bVars
      pure $ SB $ BSnoc body atom proof  newBVars
    Nothing -> Left "Clause is not well-moded."

mkHead :: SomeAtom -> Either String SomeHead
mkHead (SA atom) =
  case decPureAtom atom of
    Just prf -> pure $ SH (Head atom prf)
    Nothing   -> Left "Atom does "

-- Examples

type PMode = '[ 'Plus, 'DontCare ]

p :: Predicate PMode
p = Predicate "p" (SPlus `SCons` SDontCare `SCons` SNil)

easy :: Predicate '[ 'DontCare ]
easy = Predicate "easy" (SDontCare `SCons` SNil)

someEasy :: SomeAtom
someEasy = SA $ Atom easy (STVar (SVar (sing @"X")) `SCons` SNil)

groundP :: Atom PMode '[ 'TLit ('Lit "42"), 'TVar ('Var "X") ]
groundP = Atom p (STLit (SLit (sing @"42")) `SCons` STVar (SVar (sing @"X")) `SCons` SNil)

someGroundP :: SomeAtom
someGroundP = SA groundP

modedP :: Atom PMode '[ 'TVar ('Var "X"), 'TVar ('Var "Y") ]
modedP = Atom p (STVar (SVar (sing @"X")) `SCons` STVar (SVar (sing @"Y")) `SCons` SNil)

someModedP :: SomeAtom
someModedP = SA modedP

testCases :: [ ((SomeAtom, [ SomeAtom ]), Bool) ]
testCases =
  [ ((someEasy, [ someEasy ]), True)
  , ((someEasy, [ someModedP ]), False)
  , ((someEasy, [ someGroundP ]), True)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ someEasy, someModedP ]), True)
  , ((someEasy, [ someModedP, someEasy ]), False)
  , ((someEasy, [ someEasy, someGroundP, someModedP ]), True)
  ]

testTypes :: IO ()
testTypes = forM_ (zip testCases [(1 :: Int)..]) runTestCase
  where
  runTestCase ((testCase, expectation), ix) =
    putStrLn $
      case (uncurry mkClause testCase, expectation) of
        (Left err, True)  -> "Test #" <> show ix <> " failed."
                          <> "It should have been succesful, but \""
                          <> err <> "\"."
        (Right{} , False) -> "Test #" <> show ix <> " failed."
                          <> "It should have failed, but it passed."
        _ -> "Test passed."
