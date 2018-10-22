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
import           Data.Type.Equality ((:~:)(..), (:~~:)(..))

data instance Sing :: forall k (a :: k) (b :: k). a :~: b -> Type where
  SRefl :: Sing Refl
type (%:~:) = (Sing :: (a :: k) :~: (b :: k) -> Type)

instance SingKind (a :~: b) where
  type Demote (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl    = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

-- | Christine Paulin-Mohring's version of the J rule.
(~>:~:) :: forall k (a :: k) (b :: k)
                  (p :: forall (y :: k). a :~: y ~> Type)
                  (r :: a :~: b).
           Sing r
        -> p @@ Refl
        -> p @@ r
(~>:~:) SRefl pRefl = pRefl

data instance Sing :: forall j k (a :: j) (b :: k). a :~~: b -> Type where
  SHRefl :: Sing HRefl
type (%:~~:) = (Sing :: (a :: j) :~~: (b :: k) -> Type)

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

-- | Christine Paulin-Mohring's version of the J rule, but heterogeneously kinded.
(~>:~~:) :: forall j k (a :: j) (b :: k)
                   (p :: forall z (y :: z). a :~~: y ~> Type)
                   (r :: a :~~: b).
            Sing r
         -> p @@ HRefl
         -> p @@ r
(~>:~~:) SHRefl pHRefl = pHRefl

-----

$(singletons [d|
  type family WhySym (a :: t) (e :: a :~: (y :: t)) :: Type where
    WhySym a (_ :: a :~: y) = y :~: a

  type family WhyHsym (a :: j) (e :: a :~~: (y :: z)) :: Type where
    WhyHsym a (_ :: a :~~: y)  = y :~~: a

  type family Symmetry (x :: (a :: k) :~: (b :: k)) :: b :~: a where
    Symmetry Refl = Refl

  type family WhySymIdempotent (a :: t) (r :: a :~: (z :: t)) :: Type where
    WhySymIdempotent _ r = Symmetry (Symmetry r) :~: r

  type family Hsymmetry (x :: a :~~: b) :: b :~~: a where
    Hsymmetry HRefl = HRefl

  type family WhyHsymIdempotent (a :: j) (r :: a :~~: (y :: z)) :: Type where
    WhyHsymIdempotent _ r = Hsymmetry (Hsymmetry r) :~: r

  type family WhyReplace (from :: t) (p :: t ~> Type)
                         (e :: from :~: (y :: t)) :: Type where
    WhyReplace from p (_ :: from :~: y) = p @@ y

  -- Doesn't work due to https://ghc.haskell.org/trac/ghc/ticket/11719
  {-
  type family WhyHreplace (from :: j) (p :: forall z. z ~> Type)
                          (e :: from :~~: (y :: k)) :: Type where
    WhyHreplace from p (_ :: from :~~: y) = p @@ y
  -}

  type family WhyLeibniz (f :: t ~> Type) (a :: t) (z :: t) :: Type where
    WhyLeibniz f a z = f @@ a -> f @@ z

  type family WhyCong (f :: x ~> y) (a :: x) (e :: a :~: (z :: x)) :: Type where
    WhyCong (f :: x ~> y) (a :: x) (e :: a :~: (z :: x)) = f @@ a :~: f @@ z

  type family WhyEqIsRefl (a :: k) (e :: a :~: (z :: k)) :: Type where
    WhyEqIsRefl a e = e :~~: (Refl :: a :~: a)

  type family WhyHEqIsHRefl (a :: j) (e :: a :~~: (z :: k)) :: Type where
    WhyHEqIsHRefl a e = e :~~: (HRefl :: a :~~: a)
  |])
