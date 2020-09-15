{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnsaturatedTypeFamilies #-}
-- TODO RGS: Temporary
module Data.Singletons where

import Data.Kind
import GHC.Exts
import Unsafe.Coerce

type Sing :: k -> Type
type family Sing

type SomeSing :: Type -> Type
data SomeSing k where
  SomeSing :: Sing (a :: k) -> SomeSing k

type SingKind :: Type -> Constraint
class SingKind k where
  type Demote k = (r :: Type) | r -> k
  fromSing :: Sing (a :: k) -> Demote k
  toSing   :: Demote k -> SomeSing k

withSomeSing :: forall k r
              . SingKind k
             => Demote k
             -> (forall (a :: k). Sing a -> r)
             -> r
withSomeSing x f =
  case toSing x of
    SomeSing x' -> f x'

type SingI :: forall {k}. k -> Constraint
class SingI a where
  sing :: Sing a

type SLambda :: forall {m} k1 k2. (k1 -> @m k2) -> Type
newtype SLambda f =
  SLambda { applySing :: forall t. Sing t -> Sing (f t) }
type instance Sing = SLambda

singFun1 :: forall {m1} {a1} {b} (f :: a1 -> @m1 b). SingFunction1 f -> Sing f
singFun1 f = SLambda f

type SingFunction1 :: forall {m1} a1 b. (a1 -> @m1 b) -> Type
type SingFunction1 (f :: a1 -> b) =
  forall t. Sing t -> Sing (f t)

instance (SingKind k1, SingKind k2) => SingKind (k1 -> @U k2) where
  type Demote (k1 -> @U k2) = Demote k1 -> @U Demote k2
  fromSing sFun x = withSomeSing x (fromSing . applySing sFun)
  toSing f = SomeSing slam
    where
      slam :: forall (f :: k1 -> @U k2). Sing f
      slam = singFun1 @f lam
        where
          lam :: forall (t :: k1). Sing t -> Sing (f t)
          lam x = withSomeSing (f (fromSing x)) (\(r :: Sing res) -> unsafeCoerce r)
