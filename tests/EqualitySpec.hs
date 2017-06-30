{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module EqualitySpec where

import           Data.Kind
import           Data.Singletons
import qualified Data.Type.Equality as DTE
import           Data.Type.Equality ((:~:)(..), (:~~:)(..))

import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  describe "sym" $
    it "behaves like the one from Data.Type.Equality" $ do
      let boolEq :: Bool :~: Bool
          boolEq = Refl
      sym boolEq       `shouldBe` DTE.sym boolEq
      sym (sym boolEq) `shouldBe` DTE.sym (DTE.sym boolEq)

-----

data instance Sing (z :: a :~: b) where
  SRefl :: Sing Refl

instance SingKind (a :~: b) where
  type Demote (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl    = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

(->:~:) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y -> Type).
           Sing r
        -> p Refl
        -> p r
(->:~:) SRefl pRefl = pRefl

(~>:~:) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y ~> Type).
           Sing r
        -> p @@ Refl
        -> p @@ r
(~>:~:) SRefl pRefl = pRefl

-- (-?>:~:)

data instance Sing (z :: a :~~: b) where
  SHRefl :: Sing HRefl

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

(->:~~:) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y -> Type).
            Sing r
         -> p HRefl
         -> p r
(->:~~:) SHRefl pHRefl = pHRefl

{-
Why doesn't this typecheck?

(~>:~~:) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y ~> Type).
            Sing r
         -> p @@ HRefl
         -> p @@ r
(~>:~~:) SHRefl pHRefl = pHRefl
-}

-- (-?>:~~:)

-----

type WhySym (a :: t) (y :: t) (e :: a :~: y) = y :~: a
data WhySymSym (a :: t) :: forall (y :: t). (a :~: y) ~> Type

type instance Apply (WhySymSym z :: (z :~: y ~> Type)) x
  = WhySym z y x

sym :: forall (t :: Type) (a :: t) (b :: t).
       a :~: b -> b :~: a
sym eq = withSomeSing eq $ \(singEq :: Sing r) -> (~>:~:) @t @a @b @r @(WhySymSym a) singEq Refl
