{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}

module Data.Singletons.Prelude.List.Extras
  ( -- * Type-level functions/relations
    type DeleteAll
  , ElemR(..)
  , AllR(..)
  , Subseteq
  , Map'
    -- * Properties
  , lemListRightId
    -- * Decision procedures
  , decElem
  , decSubseteq
  , decEmpty
  ) where

import Data.Kind (Type)

import Data.Singletons.Decide
import Data.Singletons.Prelude.List

--------------------------------------------------------------------------------
-- Type-level functions/relations
--------------------------------------------------------------------------------

type family DeleteAll (x :: k) (ys :: [ k ]) :: [ k ] where
  DeleteAll x '[]       = '[]
  DeleteAll x (x ': xs) =      DeleteAll x xs
  DeleteAll x (y ': xs) = y ': DeleteAll x xs

data ElemR :: [ k ] -> k -> Type where
  Here  ::               ElemR (k ': ks) k
  There :: ElemR ks k -> ElemR (a ': ks) k

data AllR :: (k -> Type) -> [ k ] -> Type where
  Basic :: AllR p '[]
  Next  :: p k -> AllR p ks -> AllR p (k ': ks)

type Subseteq (xs :: [ k ]) (ys :: [ k ]) = AllR (ElemR ys) xs

type family Map' (f :: k -> l) (xs :: [ k ]) :: [ l ] where
  Map' _ '[]       = '[]
  Map' f (x ': xs) = f x ': Map' f xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

lemListRightId :: SList xs -> xs ++ '[] :~: xs
lemListRightId SNil                                       = Refl
lemListRightId (_ `SCons` xs) | Refl <- lemListRightId xs = Refl

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

decElem :: forall (x :: k) (xs :: [ k ])
         . SDecide k
        => Sing x -> SList xs -> Maybe (ElemR xs x)
decElem _ SNil = Nothing
decElem x (y `SCons` ys) =
  case x %~ y of
    Proved Refl -> Just Here
    _           -> There <$> decElem x ys

decSubseteq :: forall (xs :: [ k ]) (ys :: [ k ])
            . SDecide k
           => SList xs -> SList ys -> Maybe (Subseteq xs ys)
decSubseteq SNil           _  = Just Basic
decSubseteq (x `SCons` xs) ys = Next <$> decElem x ys <*> decSubseteq xs ys

decEmpty :: forall (xs :: [ k ]). SDecide k => SList xs -> Maybe (xs :~: '[])
decEmpty xs = fromDecision $ xs %~ SNil

fromDecision :: Decision k -> Maybe k
fromDecision (Proved prf) = Just prf
fromDecision _            = Nothing
