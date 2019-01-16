{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module EqualityTypes where

import           Data.Kind
import           Data.Singletons.TH
import           Data.Type.Equality ((:~~:)(..))

import           Internal

data (%:~:) :: forall k (a :: k) (b :: k). a :~: b -> Type where
  SRefl :: (%:~:) Refl
type instance Sing = (%:~:)

instance SingKind (a :~: b) where
  type Demote (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl    = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

-- | Christine Paulin-Mohring's version of the J rule.
(~>:~:) :: forall k (a :: k)
                  (p :: forall (y :: k). a :~: y ~> Type)
                  (b :: k) (r :: a :~: b).
           Sing r
        -> p @@ Refl
        -> p @@ r
(~>:~:) SRefl pRefl = pRefl

(~>!:~:) :: forall k (a :: k)
                   (p :: k ~> Prop)
                   (b :: k).
            a :~: b
         -> p @@ a
         -> p @@ b
(~>!:~:) Refl pRefl = pRefl

data (%:~~:) :: forall j k (a :: j) (b :: k). a :~~: b -> Type where
  SHRefl :: (%:~~:) HRefl
type instance Sing = (%:~~:)

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

-- | Christine Paulin-Mohring's version of the J rule, but heterogeneously kinded.
(~>:~~:) :: forall j (a :: j)
                   (p :: forall z (y :: z). a :~~: y ~> Type)
                   k (b :: k) (r :: a :~~: b).
            Sing r
         -> p @@ HRefl
         -> p @@ r
(~>:~~:) SHRefl pHRefl = pHRefl

(~>!:~~:) :: forall j (a :: j)
                    (p :: forall z. z ~> Prop)
                    k (b :: k).
             a :~~: b
          -> p @@ a
          -> p @@ b
(~>!:~~:) HRefl pHRefl = pHRefl

-----

-- These newtype wrappers are needed to work around
-- https://gitlab.haskell.org/ghc/ghc/issues/9269
newtype WrappedTrans (x :: k) (e :: x :~: y) =
  WrapTrans { unwrapTrans :: forall (z :: k). y :~: z -> x :~: z }
newtype WrappedHTrans (x :: j) (e :: x :~~: (y :: k)) =
  WrapHTrans { unwrapHTrans :: forall l (z :: l). y :~~: z -> x :~~: z }

-- This is all needed to avoid impredicativity in the defunctionalization
-- symbols for WhyHReplace and WhyHLeibniz.
newtype WrappedPred = WrapPred { unwrapPred :: forall z. z ~> Type }
type family UnwrapPred (wp :: WrappedPred) :: forall z. z ~> Type where
  forall (uwp :: forall z. z ~> Type). UnwrapPred (WrapPred uwp) = uwp

$(singletons [d|
  type WhySym (a :: t) (e :: a :~: (y :: t)) =
    y :~: a :: Type

  type WhySSym (a :: t) (e :: a :~: (y :: t)) =
    Sing (Symmetry e) :: Type

  type WhyHSym (a :: j) (e :: a :~~: (y :: z)) =
    y :~~: a :: Type

  type WhySHSym (a :: j) (e :: a :~~: (y :: z)) =
    Sing (HSymmetry e) :: Type

  type family Symmetry (x :: (a :: k) :~: (b :: k)) :: b :~: a where
    Symmetry Refl = Refl

  type WhySymIdempotent (a :: t) (r :: a :~: (z :: t)) =
    Symmetry (Symmetry r) :~: r :: Type

  type family HSymmetry (x :: a :~~: b) :: b :~~: a where
    HSymmetry HRefl = HRefl

  type WhyHSymIdempotent (a :: j) (r :: a :~~: (y :: z)) =
    HSymmetry (HSymmetry r) :~: r :: Type

  type WhyTrans (x :: k) (e :: x :~: (y :: k)) =
    WrappedTrans x e :: Type

  type WhyHTrans (x :: j) (e :: x :~~: (y :: k)) =
    WrappedHTrans x e :: Type

  type family Trans (x :: a :~: b) (y :: b :~: c) :: a :~: c where
    Trans Refl Refl = Refl

  type family HTrans (x :: a :~~: b) (y :: b :~~: c) :: a :~~: c where
    HTrans HRefl HRefl = HRefl

  type WhyReplace (from :: t) (p :: t ~> Type) (e :: from :~: (y :: t)) =
    p @@ y :: Type

  type WhyHReplace (from :: j) (p :: WrappedPred) (e :: from :~~: (y :: k)) =
    UnwrapPred p @@ y :: Type

  type WhyLeibniz (f :: t ~> Type) (a :: t) (z :: t) =
    f @@ a -> f @@ z :: Type

  type WhyHLeibniz (f :: WrappedPred) (a :: j) (b :: k) =
    UnwrapPred f @@ a -> UnwrapPred f @@ b :: Type

  type WhyCong (f :: x ~> y) (a :: x) (e :: a :~: (z :: x)) =
    f @@ a :~: f @@ z :: Type

  type WhyEqIsRefl (a :: k) (e :: a :~: (z :: k)) =
    e :~~: (Refl :: a :~: a) :: Type

  type WhyHEqIsHRefl (a :: j) (e :: a :~~: (z :: k)) =
    e :~~: (HRefl :: a :~~: a) :: Type

  type WhyTransLeft (a :: k) (e :: a :~: (z :: k)) =
    Trans e Refl :~: e :: Type

  type WhyTransLeftHelper (b :: k) (e :: b :~: (z :: k)) =
    Trans (Symmetry e) Refl :~: Symmetry e :: Type

  type WhyHTransLeft (a :: j) (e :: a :~~: (z :: k)) =
    HTrans e HRefl :~: e :: Type

  type WhyHTransLeftHelper (b :: k) (e :: b :~~: (z :: j)) =
    HTrans (HSymmetry e) HRefl :~: HSymmetry e :: Type

  type WhyTransRight (a :: k) (e :: a :~: (z :: k)) =
    Trans Refl e :~: e :: Type

  type WhyHTransRight (a :: j) (e :: a :~~: (z :: k)) =
    HTrans HRefl e :~: e :: Type

  type WhyRebalance (b :: x2 :~: x3) (c :: x3 :~: x4) (a :: x1 :~: x2) =
    Trans a (Trans b c) :~: Trans (Trans a b) c :: Type

  type WhyRebalanceHelper (b :: x2 :~: x3) (c :: x3 :~: x4) (a :: x2 :~: x1) =
    Trans (Symmetry a) (Trans b c) :~: Trans (Trans (Symmetry a) b) c :: Type

  type WhyHRebalance (b :: x2 :~~: x3) (c :: x3 :~~: x4) (a :: x1 :~~: x2) =
    HTrans a (HTrans b c) :~: HTrans (HTrans a b) c :: Type

  type WhyHRebalanceHelper (b :: x2 :~~: x3) (c :: x3 :~~: x4) (a :: x2 :~~: (x1 :: k1)) =
    HTrans (HSymmetry a) (HTrans b c) :~: HTrans (HTrans (HSymmetry a) b) c :: Type
  |])

-- These newtype wrappers are needed to work around
-- https://gitlab.haskell.org/ghc/ghc/issues/9269
newtype WrappedSTrans (x :: k) (e1 :: x :~: y) =
  WrapSTrans { unwrapSTrans :: forall (z :: k) (e2 :: y :~: z).
                               Sing e2 -> Sing (Trans e1 e2) }
newtype WrappedSHTrans (x :: j) (e1 :: x :~~: (y :: k)) =
  WrapSHTrans { unwrapSHTrans :: forall l (z :: l) (e2 :: y :~~: z).
                                 Sing e2 -> Sing (HTrans e1 e2) }

$(singletons [d|
  type WhySTrans (x :: k) (e :: x :~: (y :: k)) =
    WrappedSTrans x e :: Type

  type WhySHTrans (x :: j) (e :: x :~~: (y :: k)) =
    WrappedSHTrans x e :: Type
  |])
