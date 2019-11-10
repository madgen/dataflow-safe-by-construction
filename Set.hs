{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Set where

import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Type.Equality
import Data.Void
import Unsafe.Coerce (unsafeCoerce)

$(singletonsOnly [d|
  subseteq :: Eq a => [ a ] -> [ a ] -> Bool
  subseteq [] _ = True
  subseteq (x : xs) ys = x `elem` ys && xs `subseteq` ys

  remove :: Eq a => a -> [ a ] -> [ a ]
  remove _ [] = []
  remove x (y : ys) = if y == x then remove x ys else y : remove x ys

  exclude :: Eq a => [ a ] -> [ a ] -> [ a ]
  exclude xs [] = xs
  exclude xs (y : ys) = exclude (remove y xs) ys
  |])

{-# RULES "lemEmptySubseteq" forall xs subseteq. lemEmptySubseteq xs subseteq = unsafeCoerce Refl#-}
{-# NOINLINE lemEmptySubseteq #-}
lemEmptySubseteq :: SList xs -> Subseteq xs '[] :~: 'True  -> xs :~: '[]
lemEmptySubseteq SNil Refl = Refl
lemEmptySubseteq (_ `SCons` _) prf = absurd (falseIsNotTrue $ sym prf)

elimSubseteq :: forall k (x :: k) (xs :: [ k ]) (ys :: [ k ])
              . SEq k
             => SList (x ': xs) -> SList ys
             -> Subseteq (x ': xs) ys :~: 'True
             -> (Elem x ys :~: 'True, Subseteq xs ys :~: 'True)
elimSubseteq (x `SCons` xs) ys prf =
  case (x `sElem` ys, xs `sSubseteq` ys) of
    (STrue, STrue)   -> (Refl, Refl)
    (STrue, SFalse)  -> absurd (falseIsNotTrue $ sym prf)
    (SFalse, STrue)  -> absurd (falseIsNotTrue $ sym prf)
    (SFalse, SFalse) -> absurd (falseIsNotTrue $ sym prf)

lemNoEmptySuperset :: Subseteq (x ': xs) '[] :~: 'False
lemNoEmptySuperset = Refl

absurdSubseq :: forall k (x :: k) (xs :: [ k ])
              . SEq k
             => SList (x ': xs)
             -> Subseteq (x ': xs) '[] :~: 'True -> Void
absurdSubseq xs prf
  | xElemEmpty <- fst . elimSubseteq xs SNil $ prf =
    absurd (falseIsNotTrue (sym xElemEmpty))

falseIsNotTrue :: 'True :~: 'False -> Void
falseIsNotTrue _ = error "Unreachable"

consIsNotEmpty :: (x ': xs) :~: '[] -> Void
consIsNotEmpty _ = error "Unreachable"

lemExhaust :: forall k (xs :: [ k ]) (ys :: [ k ])
            . SEq k
           => SList xs -> SList ys
           -> Subseteq xs ys :~: 'True
           -> Exclude xs ys :~: '[]
lemExhaust xs SNil prf | Refl <- lemEmptySubseteq xs prf = Refl
lemExhaust SNil (_ `SCons` ys) prf | Refl <- lemExhaust SNil ys prf = Refl
lemExhaust (x `SCons` xs) (y `SCons` ys) prf
  | (elemPrf, subsetPrf) <- elimSubseteq (x `SCons` xs) (y `SCons` ys) prf
  , Refl <- lemExhaust xs (y `SCons` ys) subsetPrf
  , Refl <- lemExcludeTail x xs (y `SCons` ys) elemPrf = Refl

lemExcludeTail :: forall k (z :: k) (xs :: [ k ]) (ys :: [ k ])
                . SEq k
               => Sing z -> SList xs -> SList ys
               -> Elem z ys :~: 'True
               -> Exclude (z ': xs) ys :~: Exclude xs ys
lemExcludeTail _ _ SNil prf = absurd $ falseIsNotTrue (sym prf)
lemExcludeTail x xs (y `SCons` ys) prf =
  case x %== y of
    STrue -> Refl
    SFalse -> lemExcludeTail x (sRemove y xs) ys prf

lemConcatHomo :: Sing f -> SList xs -> SList ys
              -> Map f (xs ++ ys) :~: Map f xs ++  Map f ys
lemConcatHomo _ SNil _ = Refl
lemConcatHomo f (_ `SCons` xs) ys | Refl <- lemConcatHomo f xs ys = Refl
