{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Sets emulated by lists in a singleton-like interface
  -}
module Data.Singletons.Set
  ( Set
  , SSet
  , pattern SEmpty
  , pattern (:>)
    -- * Type-level functions and relations
  , type UnSet
  , type Empty
  , type In
  , type Singleton
  , type Add
  , type Union
  , type Delete
  , type (\\)
  , type AllR
  , pattern Basic
  , pattern Next
  , type ElemR
  , type Subseteq
  , type Map
    -- * Properties
  , lemSetRightId
    -- * Decision procedures
  , decElem
  , decEmpty
  , decSubseteq
  ) where

import Data.Kind (Type)

import           Data.Singletons.Decide
import qualified Data.Singletons.Prelude.List as L
import qualified Data.Singletons.Prelude.List.Extras as L

--------------------------------------------------------------------------------
-- Type-level
--------------------------------------------------------------------------------

-- Set operations

type Set a = [ a ]

type Empty = ('[] :: [ k ])

type family UnSet (set :: Set k) :: [ k ] where
  UnSet as = as

type family In (el :: k) (set :: Set k) :: Bool where
  In el set = L.Elem el set

type family Singleton (el :: k) = (res :: Set k) | res -> el where
  Singleton el = '[ el ]

type family Add (el :: k) (set :: Set k) = (res :: Set k) | res -> el set where
  Add el set = el ': set

type family Union (set1 :: Set k) (set2 :: Set k) :: Set k where
  Union set1 set2 = set1 L.++ set2

type family Delete (el :: k) (set :: Set k) :: Set k where
  Delete el set = L.DeleteAll el set

type family (set1 :: Set k) \\ (set2 :: Set k) :: Set k where
  set1 \\ '[]         = set1
  set1 \\ (el ': els) = Delete el (set1 \\ els)

type AllR (p :: k -> Type) (xs :: [ k ]) = L.AllR p xs

pattern Basic :: AllR p Empty
pattern Basic = L.Basic

pattern Next  :: p el -> AllR p set -> AllR p (Add el set)
pattern Next el prf = L.Next el prf

type ElemR (xs :: [ k ]) (x :: k) = L.ElemR xs x

type Subseteq xs ys = L.Subseteq xs ys

type Map (f :: k -> l) (xs :: Set k) = L.Map' f xs

--------------------------------------------------------------------------------
-- Singletons
--------------------------------------------------------------------------------

type SSet (set :: Set k) = L.SList set

pattern SEmpty :: () => set ~ Empty => SSet set
pattern SEmpty = L.SNil

pattern (:>) :: forall k (el :: k) (set :: Set k) (set' :: Set k)
              . (set' ~ Add el set) => (set' ~ Add el set)
             => L.Sing el -> SSet set -> SSet set'
pattern (:>) x xs = x `L.SCons` xs
{-# COMPLETE (:>), SEmpty #-}

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

lemSetRightId :: SSet set -> Union set Empty :~: set
lemSetRightId = L.lemListRightId

--------------------------------------------------------------------------------
-- Decision procedures
--------------------------------------------------------------------------------

decElem :: forall (el :: k) (set :: Set k)
         . SDecide k
        => L.Sing el -> L.SList set -> Maybe (ElemR set el)
decElem = L.decElem

decEmpty :: forall (xs :: Set k). SDecide k => SSet xs -> Maybe (xs :~: Empty)
decEmpty = L.decEmpty

decSubseteq :: forall (set1 :: Set k) (set2 :: Set k)
            . SDecide k
           => SSet set1 -> SSet set2 -> Maybe (Subseteq set1 set2)
decSubseteq = L.decSubseteq
