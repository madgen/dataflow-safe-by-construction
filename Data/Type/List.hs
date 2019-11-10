{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.List
  ( type (++)
  , type In
  , type DeleteFirst
  , type DeleteAll
  , type (\\)
  ) where

type family (xs :: [ k ]) ++ (ys :: [ k ]) :: [ k ] where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family In (x :: k) (xs :: [ k ]) where
  In _ '[]       = 'False
  In x (x ': xs) = 'True
  In x (_ ': xs) = In x xs

type family DeleteFirst (el :: k) (set :: [ k ]) :: [ k ] where
  DeleteFirst el '[]          = '[]
  DeleteFirst el (el  ': els) = els
  DeleteFirst el (el' ': els) = el' : DeleteFirst el els

type family DeleteAll (el :: k) (set :: [ k ]) :: [ k ] where
  DeleteAll el '[]         = '[]
  DeleteAll el (el  ': els) =       DeleteAll el els
  DeleteAll el (el' ': els) = el' : DeleteAll el els

type family (xs :: [ k ]) \\ (ys :: [ k ]) :: [ k ] where
  '[]       \\ ys = ys
  (x ': xs) \\ ys = DeleteFirst x (xs \\ ys)
