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
{-# LANGUAGE TemplateHaskell #-}

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
  , sDelete
  , type Difference
  , sDifference
  , type AllR
  , type ElemR
  , type Subseteq
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
import           Data.Singletons.TH

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

-- type family Delete (el :: k) (set :: Set k) :: Set k where
--   Delete el set = L.DeleteAll el set

-- type family Difference (set1 :: Set k) (set2 :: Set k) :: Set k where
--   Difference set1 '[]         = set1
--   Difference set1 (el ': els) = Difference (Delete el set1) els

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

$(singletons [d|
  delete :: Eq a => a -> [ a ] -> [ a ]
  delete _ [] = []
  delete el (el' : els) = if el' == el then delete el els else el' : delete el els

  difference :: Eq a => [ a ] -> [ a ] -> [ a ]
  difference xs [] = xs
  difference xs (y : ys) = delete y (difference xs ys)
  |])
