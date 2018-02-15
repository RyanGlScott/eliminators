{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module EqualityTypes where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Equality ((:~:)(..), (:~~:)(..))

data instance Sing (z :: a :~: b) where
  SRefl :: Sing Refl
type (%:~:) = (Sing :: (a :: k) :~: (b :: k) -> Type)

instance SingKind (a :~: b) where
  type Demote (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl    = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

-- | Christine Paulin-Mohring's version of the J rule.
(~>:~:) :: forall (k :: Type) (a :: k) (b :: k)
                  (p :: forall (y :: k). a :~: y ~> Type)
                  (r :: a :~: b).
           Sing r
        -> p @@ Refl
        -> p @@ r
(~>:~:) SRefl pRefl = pRefl

data instance Sing (z :: a :~~: b) where
  SHRefl :: Sing HRefl
type (%:~~:) = (Sing :: (a :: j) :~~: (b :: k) -> Type)

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

-- | Christine Paulin-Mohring's version of the J rule, but heterogeneously kinded.
(~>:~~:) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k)
                   (p :: forall (z :: Type) (y :: z). a :~~: y ~> Type)
                   (r :: a :~~: b).
            Sing r
         -> p @@ HRefl
         -> p @@ r
(~>:~~:) SHRefl pHRefl = pHRefl

-----

type WhySym (a :: t) (y :: t) (e :: a :~: y) = y :~: a
data WhySymSym (a :: t) :: forall (y :: t). a :~: y ~> Type
type instance Apply (WhySymSym a :: a :~: y ~> Type) x
  = WhySym a y x

type WhyHsym (a :: j) (y :: z) (e :: a :~~: y) = y :~~: a
data WhyHsymSym (a :: j) :: forall (z :: Type) (y :: z). a :~~: y ~> Type
type instance Apply (WhyHsymSym a :: a :~~: y ~> Type) x
  = WhyHsym a y x

type family Symmetry (x :: (a :: k) :~: (b :: k)) :: b :~: a where
  Symmetry Refl = Refl

type WhySymIdempotent (a :: t) (z :: t) (r :: a :~: z)
  = Symmetry (Symmetry r) :~: r
data WhySymIdempotentSym (a :: t) :: forall (z :: t). a :~: z ~> Type
type instance Apply (WhySymIdempotentSym a :: a :~: z ~> Type) r
  = WhySymIdempotent a z r

type family Hsymmetry (x :: (a :: j) :~~: (b :: k)) :: b :~~: a where
  Hsymmetry HRefl = HRefl

type WhyHsymIdempotent (a :: j) (y :: z) (r :: a :~~: y)
  = Hsymmetry (Hsymmetry r) :~: r
data WhyHsymIdempotentSym (a :: j) :: forall (z :: Type) (y :: z). a :~~: y ~> Type
type instance Apply (WhyHsymIdempotentSym a :: a :~~: y ~> Type) r
  = WhyHsymIdempotent a y r

type WhyReplace (from :: t) (p :: t ~> Type)
                (y :: t) (e :: from :~: y) = p @@ y
data WhyReplaceSym (from :: t) (p :: t ~> Type)
  :: forall (y :: t). from :~: y ~> Type
type instance Apply (WhyReplaceSym from p :: from :~: y ~> Type) x
  = WhyReplace from p y x

-- Doesn't work due to https://ghc.haskell.org/trac/ghc/ticket/11719
{-
type WhyHreplace (from :: j) (p :: forall (z :: Type). z ~> Type)
                 (y :: k) (e :: from :~~: y) = p @@ y
data WhyHreplaceSym (from :: j) (p :: forall (z :: Type). z ~> Type)
  :: forall (k :: Type) (y :: k). from :~~: y ~> Type
type instance Apply (WhyHreplaceSym from p :: from :~~: y ~> Type) x
  = WhyHreplace from p y x
-}

type WhyLeibniz (f :: t ~> Type) (a :: t) (z :: t)
  = f @@ a -> f @@ z
data WhyLeibnizSym (f :: t ~> Type) (a :: t) :: t ~> Type
type instance Apply (WhyLeibnizSym f a) z = WhyLeibniz f a z

type WhyCong (x :: Type) (y :: Type) (f :: x ~> y)
             (a :: x) (z :: x) (e :: a :~: z)
  = f @@ a :~: f @@ z
data WhyCongSym (x :: Type) (y :: Type) (f :: x ~> y)
                (a :: x) :: forall (z :: x). a :~: z ~> Type
type instance Apply (WhyCongSym x y f a :: a :~: z ~> Type) e
  = WhyCong x y f a z e

type WhyEqIsRefl (a :: k) (z :: k) (e :: a :~: z)
  = e :~~: (Refl :: a :~: a)
data WhyEqIsReflSym (a :: k) :: forall (z :: k). a :~: z ~> Type
type instance Apply (WhyEqIsReflSym a :: a :~: z ~> Type) e = WhyEqIsRefl a z e

type WhyHEqIsHRefl (a :: j) (z :: k) (e :: a :~~: z)
  = e :~~: (HRefl :: a :~~: a)
data WhyHEqIsHReflSym (a :: j) :: forall (k :: Type) (z :: k). a :~~: z ~> Type
type instance Apply (WhyHEqIsHReflSym a :: a :~~: z ~> Type) e = WhyHEqIsHRefl a z e
