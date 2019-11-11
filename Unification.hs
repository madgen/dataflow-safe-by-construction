{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}

module Unification where

import Prelude hiding (pred)

import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.TH
import           Data.Type.Equality ((:~:)(Refl), sym, TestEquality(..))
import           Data.Void

import Types
import Set

-- Substitution

data SubstitutionT         = SubstT VariableT LiteralT
data Substitution          = Subst  Variable  Literal

$(genDefunSymbols [''Substitution])

data instance Sing (x :: Substitution) where
  SSubst :: Sing var -> Sing lit -> Sing ('Subst var lit)

type SSubstitution (subst :: Substitution) = Sing subst

instance SingKind Substitution where
  type Demote Substitution = SubstitutionT
  fromSing (SSubst svar slit) = SubstT (fromSing svar) (fromSing slit)
  toSing (SubstT var lit)
    | SomeSing svar <- toSing var
    , SomeSing slit <- toSing lit = SomeSing (SSubst svar slit)

instance (SingI var, SingI lit) => SingI ('Subst var lit) where
  sing = SSubst sing sing

$(singletonsOnly [d|
  substVar :: Substitution -> Variable
  substVar (Subst var _) = var
  |])

-- Substitute into terms

$(singletonsOnly [d|
  substTerm :: Substitution -> Term -> Term
  substTerm _                t@TLit{}     = t
  substTerm (Subst var' lit) t@(TVar var) = if var == var' then TLit lit else t
  |])

-- Unifier

type Unifier (substs :: [ Substitution ]) = SList substs

data SomeUnifier vars = forall substs. SU (Unifier substs) (Map SubstVarSym0 substs :~: vars)

$(singletonsOnly [d|
  singleSubstTerms :: Substitution -> [ Term ] -> [ Term ]
  singleSubstTerms subst = map (substTerm subst)

  substTerms :: [ Term ] -> [ Substitution ] -> [ Term ]
  substTerms terms [] = terms
  substTerms terms (subst : substs) = substTerms (singleSubstTerms subst terms) substs
  |])

-- Substitute into atoms

substAtom :: Atom modes polarity terms -> Unifier substs
          -> Atom modes polarity (SubstTerms terms substs)
substAtom (Atom predicate polarity terms) unifier = Atom predicate polarity $ sSubstTerms terms unifier

-- Unification

$(singletonsOnly [d|
  consistentSubst :: Substitution -> Substitution -> Bool
  consistentSubst (Subst var lit) (Subst var' lit') = var /= var' || lit == lit'

  consistent :: Substitution -> [ Substitution ] -> Bool
  consistent subst = all (consistentSubst subst)
  |])

type family MakeSubsts (ts :: [ Term ]) (ls :: [ Literal ]) :: [ Substitution ] where
  MakeSubsts '[] '[] = '[]
  MakeSubsts ('TLit _   ': ts)  (_   ': ls) = MakeSubsts ts ls
  MakeSubsts ('TVar var ': ts)  (lit ': ls) = 'Subst var lit ': MakeSubsts ts ls

sUnifyTerms :: STerms terms -> STerms terms'
             -> KeepVars terms' :~: '[]
             -> Maybe (SomeUnifier (KeepVars terms))
sUnifyTerms SNil SNil _ = Just (SU SNil Refl)
sUnifyTerms (STLit l `SCons` ts) (STLit l' `SCons` ls) prf =
  case l %== l' of
    STrue  -> sUnifyTerms ts ls prf
    SFalse -> Nothing
sUnifyTerms (STVar v `SCons` ts) (STLit l  `SCons` ls) noVarsPrf = do
  SU unifier Refl <- sUnifyTerms ts ls noVarsPrf
  let subst = SSubst v l
  case subst `sConsistent` unifier of
    STrue -> pure $ SU (subst `SCons` unifier) Refl
    SFalse -> Nothing
sUnifyTerms _ (STVar _ `SCons` _) prf = absurd (absurdList prf)
sUnifyTerms _ _ _ = Nothing

absurdList :: (x ': xs) :~: '[] -> Void
absurdList _ = error "Inaccessible"

unify :: Atom modes polarity terms -> Tuple -> Maybe (SomeUnifier (KeepVars terms))
unify (Atom pred _ sTerms) (Tuple (Atom pred' SPositive sTerms') prf) = do
 Refl <- pred `testEquality` pred'
 sUnifyTerms sTerms sTerms' prf

-- Properties of substitution

lemSingleSubstLen :: forall terms subst
                   . STerms terms -> SSubstitution subst
                  -> Length terms :~: Length (SingleSubstTerms subst terms)
lemSingleSubstLen SNil _ = Refl
lemSingleSubstLen (_ `SCons` ts) subst | Refl <- lemSingleSubstLen ts subst = Refl

lemSubstPreservesLen :: STerms terms -> Unifier unifier
                     -> Length terms :~: Length (SubstTerms terms unifier)
lemSubstPreservesLen _ SNil = Refl
lemSubstPreservesLen sTerms (sSubst `SCons` sSubsts)
  | Refl <- lemSubstPreservesLen (sSingleSubstTerms sSubst sTerms) sSubsts
  , Refl <- lemSingleSubstLen sTerms sSubst = Refl

lemSingleSubstOnVars :: STerms terms -> SSubstitution subst
                     -> KeepVars (SingleSubstTerms subst terms) :~: Remove (SubstVar subst) (KeepVars terms)
lemSingleSubstOnVars SNil _ = Refl
lemSingleSubstOnVars (STLit{} `SCons` ts) subst | Refl <- lemSingleSubstOnVars ts subst = Refl
lemSingleSubstOnVars (STVar var `SCons` ts) subst@(SSubst var' _) | Refl <- lemSingleSubstOnVars ts subst =
  case var %== var' of
    STrue  -> Refl
    SFalse -> Refl

lemSubstOnVars :: STerms terms -> Unifier unifier
               -> KeepVars (SubstTerms terms unifier) :~: Exclude (KeepVars terms) (Map SubstVarSym0 unifier)
lemSubstOnVars _ SNil = Refl
lemSubstOnVars sTerms (sSubst `SCons` sSubsts)
  | Refl <- sym $ lemSingleSubstOnVars sTerms sSubst
  , Refl <- lemSubstOnVars (sSingleSubstTerms sSubst sTerms) sSubsts = Refl

lemCompleteSubst :: STerms terms -> Unifier substs
                 -> Subseteq (KeepVars terms) (Map SubstVarSym0 substs) :~: 'True
                 -> KeepVars (SubstTerms terms substs) :~: '[]
lemCompleteSubst terms substs subseteq
  | Refl <- lemSubstOnVars terms substs
  , Refl <- lemExhaust (sKeepVars terms) (sMap (sing @SubstVarSym0) substs) subseteq = Refl

-- Useful instances

$(singletonsOnly [d|
  instance Eq Substitution where
    Subst var lit == Subst var' lit' = var == var' && lit == lit'

  instance Ord Substitution where
    Subst var lit `compare` Subst var' lit' = (var, lit) `compare` (var', lit')
  |])

instance Eq (SomeUnifier vars) where
  SU unifier _ == SU unifier' _ = fromSing (unifier %== unifier')

instance Ord (SomeUnifier vars) where
  SU unifier _ `compare` SU unifier' _ = fromSing (unifier `sCompare` unifier')
