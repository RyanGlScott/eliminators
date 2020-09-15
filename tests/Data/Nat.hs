{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- TODO RGS: Temporary
module Data.Nat where

import Data.Kind
import Data.Singletons
import Data.Singletons.Prelude.Num
import qualified GHC.TypeNats as GHC

type Nat :: Type
data Nat = Z | S Nat

type SNat :: Nat -> Type
data SNat z where
  SZ :: SNat Z
  SS :: Sing x -> SNat (S x)
type instance Sing = SNat

instance SingI Z where
  sing = SZ
instance SingI n => SingI (S n) where
  sing = SS sing

type Lit :: GHC.Nat -> Nat
type family Lit n where
  Lit 0 = Z
  Lit n = S (Lit (n GHC.- 1))

sLit :: SingI (Lit n) => Sing (Lit n)
sLit = sing

type NatPlus :: Nat -> Nat -> Nat
type family NatPlus x y where
  NatPlus Z     b = b
  NatPlus (S a) b = S (NatPlus a b)

type NatMul :: Nat -> Nat -> Nat
type family NatMul x y where
  NatMul Z     _ = Z
  NatMul (S a) b = NatPlus b (NatMul a b)

instance PNum Nat where
  type x + y = NatPlus x y
  type x * y = NatMul  x y
