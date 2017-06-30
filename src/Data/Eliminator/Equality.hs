{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Eliminator.Equality where

import Data.Eliminator
import Data.Kind
import Data.Singletons
import Data.Type.Equality ((:~:)(..), (:~~:)(..))

data instance Sing (z :: a :~: b) where
  SRefl :: Sing Refl

(%:~:->) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y -> Type).
            Sing r
         -> p Refl
         -> p r
(%:~:->) SRefl pRefl = pRefl

(%:~:~>) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y ~> Type).
            Sing r
         -> p @@ Refl
         -> p @@ r
(%:~:~>) SRefl pRefl = pRefl

-- (%:~:-?>)

data instance Sing (z :: a :~~: b) where
  SHRefl :: Sing HRefl

(%:~~:->) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y -> Type).
             Sing r
          -> p HRefl
          -> p r
(%:~~:->) SHRefl pHRefl = pHRefl

{-
Why doesn't this typecheck?

(%:~~:~>) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y ~> Type).
             Sing r
          -> p @@ HRefl
          -> p @@ r
(%:~~:~>) SHRefl pHRefl = pHRefl
-}

-- (%:~~:-?>)
