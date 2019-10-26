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
    -- * Type-level operations
  , type UnSet
  , type Empty
  , type In
  , type Singleton
  , type Add
  , type Union
  , type Delete
  , type (\\)
  , type AllR
  , type ElemR
  , type Subseteq
    -- * Singletons
  , pattern SEmpty
  , pattern (:>)
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
  set1 \\ (el ': els) = (Delete el set1) \\ els

type AllR (p :: k -> Type) (xs :: [ k ]) = L.AllR p xs

type ElemR (xs :: [ k ]) (x :: k) = L.ElemR xs x

type Subseteq xs ys = L.Subseteq xs ys

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
-- Decision procedures
--------------------------------------------------------------------------------

decSubseteq :: forall (set1 :: Set k) (set2 :: Set k)
            . SDecide k
           => SSet set1 -> SSet set2 -> Maybe (Subseteq set1 set2)
decSubseteq = L.decSubseteq
