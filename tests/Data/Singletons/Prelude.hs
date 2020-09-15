{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- TODO RGS: Temporary
module Data.Singletons.Prelude
  ( module Data.Singletons
  , module Data.Singletons.Prelude
  ) where

import Data.Kind
import Data.Singletons
import Data.Void

type SBool :: Bool -> Type
data SBool z where
  SFalse :: SBool False
  STrue  :: SBool True
type instance Sing = SBool
instance SingKind Bool where
  type Demote Bool = Bool
  fromSing SFalse = False
  fromSing STrue  = True
  toSing False = SomeSing SFalse
  toSing True  = SomeSing STrue

type SList :: [a] -> Type
data SList z where
  SNil  :: SList '[]
  SCons :: Sing x -> Sing xs -> SList (x:xs)
type instance Sing = SList

type SVoid :: Void -> Type
data SVoid z
type instance Sing = SVoid
instance SingKind Void where
  type Demote Void = Void
  fromSing v = case v of {}
  toSing   v = case v of {}

type Const :: a -> b -> a
type family Const x y where
  Const x _ = x

type Flip :: (a -> b -> c) -> b -> a -> c
type family Flip f x y where
  Flip f x y = f y x

type (.) :: (b -> c) -> (a -> b) -> a -> c
type family (f . g) x where
  (f . g) x = f (g x)
