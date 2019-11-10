{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Set
  ( Set
  , type Add
  , type Union
  , type Delete
  , type (\\)
  ) where

import qualified Data.Type.List as TL

newtype Set a = Set [ a ]

type family In (el :: k) (set :: Set k) :: Bool where
  In el ('Set set) = TL.In el set

type family Add (el :: k) (els :: Set k) :: Set k where
  Add el ('Set els) = 'Set (el ': els)

type family Union (set1 :: Set k) (set2 :: Set k) :: Set k where
  Union ('Set set1) ('Set set2) = 'Set (set1 TL.++ set2)

type family Delete (el :: k) (set :: Set k) :: Set k where
  Delete el ('Set els) = 'Set (TL.DeleteAll  el els)

type family (set1 :: Set k) \\ (set2 :: Set k) :: Set k where
  set1 \\ ('Set '[])         = set1
  set1 \\ ('Set (el ': els)) = Delete el (set1 \\ 'Set els)
