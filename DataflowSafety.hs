{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

module DataflowSafety where

import Data.Kind
import Data.Proxy
import Data.Void
import Data.Type.Equality

import GHC.TypeLits

type Var = Symbol

data Term = TVar | TLit

data STerm :: (Term,Symbol) -> Type where
  STVar :: Proxy sym -> STerm '(TVar, sym)
  STLit :: Proxy sym -> STerm '(TLit, sym)

type family IxListConstraint (a :: k) :: Constraint where
  IxListConstraint (sym :: Symbol)                    = KnownSymbol sym
  IxListConstraint '((term :: Term), (sym :: Symbol)) = KnownSymbol sym

type TermList (terms :: [ (Term, Symbol) ]) = IxList '[] (:) STerm terms

type family Vars (terms :: [ (Term, Symbol) ]) :: [ Var ] where
  Vars '[]                  = '[]
  Vars ('( 'TVar, sym) ': terms) = sym ': Vars terms
  Vars ('( 'TLit, _)   ': terms) = Vars terms

type VarList (vars :: [ Var ]) = IxList '[] (:) Proxy vars

filterVars :: TermList terms -> VarList (Vars terms)
filterVars INil               = INil
filterVars (STVar v :> terms) = v :> filterVars terms

data Mode = MPlus | MDontCare

data SMode :: Mode -> Type where
  SMPlus     :: SMode MPlus
  SMDontCare :: SMode MDontCare

class Trivial (a :: k)

type ModeList (modes :: [ Mode ]) = IxList '[] (:) SMode modes

data Predicate (modes :: [ Mode ]) = Predicate String (ModeList modes)

type family ModedVars (modes :: [ Mode ]) (terms :: [ (Term, Symbol) ]) :: [ Var ] where
  ModedVars '[]                   '[]                       = '[]
  ModedVars ('MDontCare ': modes) (_ ': terms)              = ModedVars modes terms
  ModedVars (_ ': modes)          ('( 'TLit, _) ': terms)   = ModedVars modes terms
  ModedVars ('MPlus ': modes)     ('( 'TVar, var) ': terms) = var ': ModedVars modes terms
  ModedVars _ _ = TypeError (Text "Modes and terms are not of equal length.")

type ModedVarList modes terms = IxList '[] (:) Proxy (ModedVars modes terms)

modedVars :: Predicate modes -> TermList terms -> ModedVarList modes terms
modedVars (Predicate _ modeList) termList = go modeList termList
  where
  go :: ModeList modes -> TermList terms -> ModedVarList modes terms
  go INil                     INil                    = INil
  go (SMDontCare :> modeList) (_ :> termList)         = go modeList termList
  go (_ :> modeList)          (STLit{}   :> termList) = go modeList termList
  go (SMPlus :> modeList)     (STVar var :> termList) = var :> go modeList termList
  go _ _ = error "Mode and term list size mismatch"

data Atom :: [ Var ] -> [ Var ] -> Type where
  Atom :: Predicate modes
       -> TermList terms
       -> Atom (ModedVars modes terms) (Vars terms)

vars :: Atom modedVars vars -> VarList vars
vars (Atom _ termList) = filterVars termList

data AlmostSomeAtom modedVars = forall vars          . ASA (Atom modedVars vars)
data SomeAtom                 = forall vars modedVars. SA  (Atom modedVars vars)

type BodyVarList (vars :: [ Var ]) = IxList '[] (:) Proxy vars

data Body :: [ Var ] -> Type where
  EmptyBody :: Body '[]
  SnocBody  :: Body bodyVars
            -> Atom modedVars atomVars
            -> AllElem modedVars bodyVars -- Well-modedness
            -> BodyVarList (atomVars :++: bodyVars)
            -> Body (atomVars :++: bodyVars)

data SomeBody = forall bodyVars. SB (Body bodyVars)

data Clause :: Type where
  Clause :: Atom '[] headVars
         -> Body bodyVars
         -> AllElem headVars bodyVars -- Range restriction
         -> Clause

mkClause :: SomeAtom -> [ SomeAtom ] -> Maybe Clause
mkClause  someHead bodyAtoms = do
  SB body  <- mkBody $ reverse bodyAtoms
  ASA head <- mkHead someHead
  proof <- checkRangeRestriction head body
  pure $ Clause head body proof
  where
  mkBody :: [ SomeAtom ] -> Maybe SomeBody
  mkBody [] = Just $ SB EmptyBody
  mkBody (SA atom@(Atom predicate terms) : atoms) = do
    let modedVarList = modedVars predicate terms
    let varList = vars atom
    SB body <- mkBody atoms
    case body of
      EmptyBody | Refl <- lemEmptyRight varList -> do
        Refl <- decEmpty modedVarList
        pure $ SB $ SnocBody body atom Basic varList
      SnocBody _ _ _ bodyVarList -> do
        proof <- decAllElem modedVarList bodyVarList
        pure $ SB $ SnocBody body atom proof (varList `append` bodyVarList)

  mkHead :: SomeAtom -> Maybe (AlmostSomeAtom '[])
  mkHead (SA atom@(Atom predicate terms)) =
    case decEmpty (modedVars predicate terms) of
      Just Refl -> Just $ ASA atom
      Nothing   -> Nothing

  checkRangeRestriction :: Atom '[] headVars
                        -> Body bodyVars
                        -> Maybe (AllElem headVars bodyVars)
  checkRangeRestriction atom body =
    case body of
      EmptyBody -> do
        Refl <- decEmpty $ vars atom
        pure $ Basic
      SnocBody _ _ _ bodyVars -> decAllElem (vars atom) bodyVars

--------------------------------------------------------------------------------
-- Blah
--------------------------------------------------------------------------------

type family (xs :: [ k ]) :++: (ys :: [ k ]) :: [ k ] where
  '[]       :++: ys = ys
  (x ': xs) :++: ys = x ': (xs :++: ys)

infixr 6 :>

data IxList :: b -> (a -> b -> b) -> (a -> Type) -> b -> Type where
  INil ::                                                IxList e f c e
  (:>) :: IxListConstraint a => c a -> IxList e f c b -> IxList e f c (f a b)

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

data All :: (k -> Type) -> [ k ] -> Type where
  Basic :: All p '[]
  Next  :: p k -> All p ks -> All p (k ': ks)

decAllElem :: VarList vars -> VarList vars' -> Maybe (AllElem vars vars')
decAllElem INil ys      = Just Basic
decAllElem (x :> xs) ys =
  case (decElem x ys, decAllElem xs ys) of
    (Just elem, Just allElem) -> Just $ Next elem allElem
    _ -> Nothing

decEmpty :: IxList '[] f a xs -> Maybe (xs :~: '[])
decEmpty INil = Just Refl
decEmpty _    = Nothing

type AllElem xs ys = All (Elem ys) xs

lemEmptyRight :: IxList '[] (:) p xs -> xs :++: '[] :~: xs
lemEmptyRight INil                            = Refl
lemEmptyRight (x :> xs) | Refl <- lemEmptyRight xs = Refl
