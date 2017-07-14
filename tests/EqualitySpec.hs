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

(~>:~:) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y ~> Type).
           Sing r
        -> p @@ Refl
        -> p @@ r
(~>:~:) SRefl pRefl = pRefl

data instance Sing (z :: a :~~: b) where
  SHRefl :: Sing HRefl

instance SingKind (a :~~: b) where
  type Demote (a :~~: b) = a :~~: b
  fromSing SHRefl = HRefl
  toSing HRefl    = SomeSing SHRefl

instance SingI HRefl where
  sing = SHRefl

(~>:~~:) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y ~> Type).
            Sing r
         -> p @@ HRefl
         -> p @@ r
(~>:~~:) SHRefl pHRefl = pHRefl

-----

type WhySym (a :: t) (y :: t) (e :: a :~: y) = y :~: a
data WhySymSym (a :: t) :: forall (y :: t). a :~: y ~> Type
type instance Apply (WhySymSym z :: z :~: y ~> Type) x
  = WhySym z y x

sym :: forall (t :: Type) (a :: t) (b :: t).
       a :~: b -> b :~: a
sym eq = withSomeSing eq $ \(singEq :: Sing r) ->
           (~>:~:) @t @a @b @r @(WhySymSym a) singEq Refl

type family Symmetry (x :: (a :: k) :~: (b :: k)) :: b :~: a where
  Symmetry Refl = Refl

type WhySymIdempotent (a :: t) (z :: t) (r :: a :~: z)
  = Symmetry (Symmetry r) :~: r
data WhySymIdempotentSym (a :: t) :: forall (z :: t). a :~: z ~> Type
type instance Apply (WhySymIdempotentSym a :: a :~: z ~> Type) r
  = WhySymIdempotent a z r

symIdempotent :: forall (t :: Type) (a :: t) (b :: t)
                        (e :: a :~: b).
                 Sing e -> Symmetry (Symmetry e) :~: e
symIdempotent se = (~>:~:) @t @a @b @e @(WhySymIdempotentSym a) se Refl

type WhyReplace (from :: t) (p :: t ~> Type)
                (y :: t) (e :: from :~: y) = p @@ y
data WhyReplaceSym (from :: t) (p :: t ~> Type)
  :: forall (y :: t). from :~: y ~> Type
type instance Apply (WhyReplaceSym from p :: from :~: y ~> Type) x
  = WhyReplace from p y x

replace :: forall (t :: Type) (from :: t) (to :: t) (p :: t ~> Type).
           p @@ from
        -> from :~: to
        -> p @@ to
replace from eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @t @from @to @r @(WhyReplaceSym from p) singEq from

type WhyLeibniz (f :: t ~> Type) (a :: t) (z :: t)
  = f @@ a -> f @@ z
data WhyLeibnizSym (f :: t ~> Type) (a :: t) :: t ~> Type
type instance Apply (WhyLeibnizSym f a) z = WhyLeibniz f a z

leibniz :: forall (t :: Type) (f :: t ~> Type) (a :: t) (b :: t).
           a :~: b
        -> f @@ a
        -> f @@ b
leibniz = replace @t @a @b @(WhyLeibnizSym f a) id

type WhyCong (x :: Type) (y :: Type) (f :: x ~> y)
             (a :: x) (z :: x) (e :: a :~: z)
  = f @@ a :~: f @@ z
data WhyCongSym (x :: Type) (y :: Type) (f :: x ~> y)
                (a :: x) :: forall (z :: x). a :~: z ~> Type
type instance Apply (WhyCongSym x y f a :: a :~: z ~> Type) e
  = WhyCong x y f a z e

cong :: forall (x :: Type) (y :: Type) (f :: x ~> y)
               (a :: x) (b :: x).
        a :~: b
     -> f @@ a :~: f @@ b
cong eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @x @a @b @r @(WhyCongSym x y f a) singEq Refl
