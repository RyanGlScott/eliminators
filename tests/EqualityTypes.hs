{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnsaturatedTypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module EqualityTypes where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Equality ((:~:)(..), (:~~:)(..))

import           Internal

type (%:~:) :: a :~: b -> Type
data (%:~:) e where
  SRefl :: (%:~:) Refl
type instance Sing = (%:~:)

instance SingKind (a :~: b) where
  type Demote (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl    = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

-- | Christine Paulin-Mohring's version of the J rule.
(~>:~:) :: forall {m} k (a :: k)
                  (p :: forall (y :: k). a :~: y -> @m Type)
                  (b :: k) (r :: a :~: b).
           Sing r
        -> p Refl
        -> p r
(~>:~:) SRefl pRefl = pRefl

type (~>:~:) :: forall k (a :: k).
                forall (p :: forall (y :: k). a :~: y -> Type)
             -> forall (b :: k).
                forall (r :: a :~: b)
             -> p Refl
             -> p r
type family (~>:~:) p r pRefl where
  forall k (a :: k)
         (p :: forall (y :: k). a :~: y -> Type)
         (pRefl :: p Refl).
    (~>:~:) p Refl pRefl = pRefl

(~>!:~:) :: forall {m} k (a :: k)
                   (p :: k -> @m Prop)
                   (b :: k).
            a :~: b
         -> p a
         -> p b
(~>!:~:) Refl pRefl = pRefl

type (~>!:~:) :: forall k (a :: k).
                 forall (p :: k -> Prop)
              -> forall (b :: k).
                 a :~: b
              -> p a
              -> p b
type family (~>!:~:) p r pRefl where
  (~>!:~:) _ Refl pRefl = pRefl

type (%:~~:) :: forall j k (a :: j) (b :: k). a :~~: b -> Type
data (%:~~:) e where
  SHRefl :: (%:~~:) HRefl
type instance Sing = (%:~~:)

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

-- | Christine Paulin-Mohring's version of the J rule, but heterogeneously kinded.
(~>:~~:) :: forall {m} j (a :: j)
                   (p :: forall z (y :: z). a :~~: y -> @m Type)
                   k (b :: k) (r :: a :~~: b).
            Sing r
         -> p HRefl
         -> p r
(~>:~~:) SHRefl pHRefl = pHRefl

type (~>:~~:) :: forall {m} j (a :: j).
                 forall (p :: forall z (y :: z). a :~~: y -> @m Type)
              -> forall k (b :: k).
                 forall (r :: a :~~: b)
              -> p HRefl
              -> p r
type family (~>:~~:) p r pHRefl where
  forall j (a :: j)
         (p :: forall z (y :: z). a :~~: y -> Type)
         (pHRefl :: p HRefl).
    (~>:~~:) p HRefl pHRefl = pHRefl

(~>!:~~:) :: forall {m} j (a :: j)
                    (p :: forall z. z -> @m Prop)
                    k (b :: k).
             a :~~: b
          -> p a
          -> p b
(~>!:~~:) HRefl pHRefl = pHRefl

type (~>!:~~:) :: forall {m} j (a :: j).
                  forall (p :: forall z. z -> @m Prop)
               -> forall k (b :: k).
                  a :~~: b
               -> p a
               -> p b
type family (~>!:~~:) p r pHRefl where
  forall j (a :: j)
         (p :: forall z. z -> Prop)
         (pHRefl :: p a).
    (~>!:~~:) p (HRefl :: a :~~: a) pHRefl = pHRefl

-----

-- These newtype wrappers are needed to work around
-- https://gitlab.haskell.org/ghc/ghc/issues/9269
type WrappedTrans :: forall k (x :: k) (y :: k). x :~: y -> Type
newtype WrappedTrans (e :: (x :: k) :~: y) =
  WrapTrans (forall (z :: k). y :~: z -> x :~: z)

type WrappedHTrans :: forall j (x :: j) k (y :: k). x :~~: y -> Type
newtype WrappedHTrans (e :: x :~~: y) =
  WrapHTrans (forall l (z :: l). y :~~: z -> x :~~: z)

unwrapTrans :: WrappedTrans (e :: (x :: k) :~: y)
            -> forall (z :: k). y :~: z -> x :~: z
unwrapTrans (WrapTrans f) = f

type UnwrapTrans ::
  forall k (x :: k) (y :: k) (e :: x :~: y).
  WrappedTrans e -> forall (z :: k). y :~: z -> x :~: z
type family UnwrapTrans wt :: forall z. y :~: z -> x :~: z where
  forall k (x :: k) (y :: k) (uwt :: forall (z :: k). y :~: z -> x :~: z).
    UnwrapTrans (WrapTrans uwt) = uwt

unwrapHTrans :: WrappedHTrans (e :: x :~~: y)
             -> forall l (z :: l). y :~~: z -> x :~~: z
unwrapHTrans (WrapHTrans f) = f

type UnwrapHTrans ::
  forall j (x :: j) k (y :: k) (e :: x :~~: y).
  WrappedHTrans e -> forall l (z :: l). y :~~: z -> x :~~: z
type family UnwrapHTrans wht :: forall l (z :: l). y :~~: z -> x :~~: z where
  forall j (x :: j) k (y :: k) (uwht :: forall l (z :: l). y :~~: z -> x :~~: z).
    UnwrapHTrans (WrapHTrans uwht) = uwht

-- This is all needed to avoid impredicativity in the defunctionalization
-- symbols for WhyHReplace and WhyHLeibniz.
type WrappedPred :: Type
newtype WrappedPred = WrapPred { unwrapPred :: forall z. z -> Type }

type UnwrapPred :: WrappedPred -> forall z. z -> Type
type family UnwrapPred wp :: forall z. z -> Type where
  forall (uwp :: forall z. z -> Type). UnwrapPred (WrapPred uwp) = uwp

type WhySym :: forall t (a :: t) (y :: t). a :~: y -> Type
type WhySym (e :: a :~: y) = y :~: a

type WhyHSym :: forall j (a :: j) t (y :: t). a :~~: y -> Type
type WhyHSym (e :: a :~~: y) = y :~~: a

type TransStep :: forall k (x :: k) (z :: k). x :~: z -> x :~: z
type TransStep e = e

type HTransStep :: forall j (x :: j) k (z :: k). x :~~: z -> x :~~: z
type HTransStep e = e

-- These use eliminators, but th-desugar takes a while to expand them.
-- TODO RGS: Investigate why.
{-
type Trans :: a :~: b -> b :~: c -> a :~: c
type Trans x y =
  UnwrapTrans ((~>:~:) PWrappedTransSym0 x (WrapTrans TransStepSym0)) @@ y

type HTrans :: a :~~: b -> b :~~: c -> a :~~: c
type HTrans x y =
  UnwrapHTrans ((~>:~~:) PWrappedHTransSym0 x (WrapHTrans HTransStepSym0)) @@ y
-}

type Trans :: a :~: b -> b :~: c -> a :~: c
type family Trans x y where
  Trans Refl Refl = Refl

type HTrans :: a :~~: b -> b :~~: c -> a :~~: c
type family HTrans x y where
  HTrans HRefl HRefl = HRefl

type WhyReplace :: forall t. forall (from :: t)
                -> (t -> Type)
                -> forall (y :: t). from :~: y
                -> Type
type WhyReplace from p (e :: from :~: y) = p y

type WhyHReplace :: forall j. forall (from :: j)
                 -> WrappedPred
                 -> forall k (y :: k). from :~~: y
                 -> Type
type WhyHReplace from p (e :: from :~~: y) = UnwrapPred p y

type WhyLeibniz :: (t -> Type) -> t -> t -> Type
type WhyLeibniz f a z = f a -> f z

type WhyHLeibniz :: WrappedPred
                 -> forall j. j
                 -> forall k. k
                 -> Type
type WhyHLeibniz f a b = UnwrapPred f a -> UnwrapPred f b

type WhyCong :: (x -> y) -> forall (a :: x) (z :: x). a :~: z -> Type
type WhyCong f (e :: a :~: z) = f a :~: f z

type WhyEqIsRefl :: forall k (a :: k) (z :: k). a :~: z -> Type
type WhyEqIsRefl (e :: a :~: z) = e :~~: (Refl :: a :~: a)

type WhyHEqIsHRefl :: forall j (a :: j) k (z :: k). a :~~: z -> Type
type WhyHEqIsHRefl (e :: a :~~: z) = e :~~: (HRefl :: a :~~: a)

type WhyTransLeft :: forall k (a :: k) (z :: k). a :~: z -> Type
type WhyTransLeft e = Trans e Refl :~: e

type WhyHTransLeft :: forall j (a :: j) k (z :: k). a :~~: z -> Type
type WhyHTransLeft e = HTrans e HRefl :~: e

type WhyTransRight :: forall k (a :: k) (z :: k). a :~: z -> Type
type WhyTransRight e = Trans Refl e :~: e

type WhyHTransRight :: forall j (a :: j) k (z :: k). a :~~: z -> Type
type WhyHTransRight e = HTrans HRefl e :~: e

type WhyRebalance :: x2 :~: x3 -> x3 :~: x4 -> x1 :~: x2 -> Type
type WhyRebalance b c a = Trans a (Trans b c) :~: Trans (Trans a b) c

type WhyHRebalance :: x2 :~~: x3 -> x3 :~~: x4 -> x1 :~~: x2 -> Type
type WhyHRebalance b c a = HTrans a (HTrans b c) :~: HTrans (HTrans a b) c

-- TODO RGS: These fail to typecheck due to https://gitlab.haskell.org/kcsongor/ghc/-/issues/18
{-
type Symmetry :: a :~: b -> b :~: a
type Symmetry  (r :: a :~: b) = (~>:~:) WhySym r Refl

type HSymmetry :: a :~~: b -> b :~~: a
type HSymmetry (r :: a :~~: b) = (~>:~~:) WhyHSym r HRefl
-}

-- These newtype wrappers are needed to work around
-- https://gitlab.haskell.org/ghc/ghc/issues/9269
type WrappedSTrans :: forall k (x :: k) (y :: k). x :~: y -> Type
newtype WrappedSTrans (e1 :: (x :: k) :~: y) =
  WrapSTrans { unwrapSTrans :: forall (z :: k) (e2 :: y :~: z).
                               Sing e2 -> Sing (Trans e1 e2) }

type WrappedSHTrans :: forall j (x :: j) k (y :: k). x :~~: y -> Type
newtype WrappedSHTrans (e1 :: x :~~: y) =
  WrapSHTrans { unwrapSHTrans :: forall l (z :: l) (e2 :: y :~~: z).
                                 Sing e2 -> Sing (HTrans e1 e2) }

{-
type WhySSym :: forall t (a :: t) (y :: t). a :~: y -> Type
type WhySSym e = Sing (Symmetry e)

type WhySymIdempotent :: forall t (a :: t) (z :: t). a :~: z -> Type
type WhySymIdempotent r = Symmetry (Symmetry r) :~: r

type WhySHSym :: forall j (a :: j) z (y :: z). a :~~: y -> Type
type WhySHSym e = Sing (HSymmetry e)

type WhyHSymIdempotent :: forall j (a :: j) z (y :: z). a :~~: y -> Type
type WhyHSymIdempotent r = HSymmetry (HSymmetry r) :~: r

type WhyTransLeftHelper :: forall k (b :: k) (z :: k). b :~: z -> Type
type WhyTransLeftHelper e = Trans (Symmetry e) Refl :~: Symmetry e

type WhyHTransLeftHelper :: forall k. forall (b :: k) j (z :: j). b :~~: z -> Type
type WhyHTransLeftHelper e = HTrans (HSymmetry e) HRefl :~: HSymmetry e

type WhySTrans :: forall k (x :: k) (y :: k). x :~: y -> Type
type WhySTrans e = WrappedSTrans e

type WhySHTrans :: forall j (x :: j) k (y :: k). x :~~: y -> Type
type WhySHTrans e = WrappedSHTrans e

type WhyRebalanceHelper :: x2 :~: x3 -> x3 :~: x4 -> forall x1. x2 :~: x1 -> Type
type WhyRebalanceHelper b c a =
  Trans (Symmetry a) (Trans b c) :~: Trans (Trans (Symmetry a) b) c

type WhyHRebalanceHelper :: x2 :~~: x3 -> x3 :~~: x4 -> forall k1 (x1 :: k1). x2 :~~: x1 -> Type
type WhyHRebalanceHelper b c a =
  HTrans (HSymmetry a) (HTrans b c) :~: HTrans (HTrans (HSymmetry a) b) c
-}
