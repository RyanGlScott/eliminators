{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module EqualitySpec where

import           Data.Kind
import           Data.Singletons
import qualified Data.Type.Equality as DTE
import           Data.Type.Equality ((:~:)(..), (:~~:)(..))

import           EqualityTypes
import           Internal

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

j :: forall k (p :: forall (x :: k) (y :: k). x :~: y ~> Type)
            (a :: k) (b :: k)
            (r :: a :~: b).
     Sing r
  -> (forall (x :: k). p @@ (Refl :: x :~: x))
  -> p @@ r
j SRefl pRefl = pRefl @a

jProp :: forall k (p :: k ~> k ~> Prop)
                (a :: k) (b :: k).
         a :~: b
      -> (forall (x :: k). p @@ x @@ x)
      -> p @@ a @@ b
jProp Refl pRefl = pRefl @a

hj :: forall (p :: forall y z (w :: y) (x :: z). w :~~: x ~> Type)
             j k (a :: j) (b :: k)
             (r :: a :~~: b).
      Sing r
   -> (forall y (w :: y). p @@ (HRefl :: w :~~: w))
   -> p @@ r
hj SHRefl pHRefl = pHRefl @j @a

hjProp :: forall (p :: forall y z. y ~> z ~> Prop)
                 j k (a :: j) (b :: k).
          a :~~: b
       -> (forall y (w :: y). p @@ w @@ w)
       -> p @@ a @@ b
hjProp HRefl pHRefl = pHRefl @j @a

k :: forall k (a :: k)
            (p :: a :~: a ~> Type)
            (r :: a :~: a).
     Sing r
  -> p @@ Refl
  -> p @@ r
k SRefl pRefl = pRefl

hk :: forall k (a :: k)
             (p :: a :~~: a ~> Type)
             (r :: a :~~: a).
      Sing r
   -> p @@ HRefl
   -> p @@ r
hk SHRefl pHRefl = pHRefl

sym :: forall t (a :: t) (b :: t).
       a :~: b -> b :~: a
sym eq = withSomeSing eq $ \(singEq :: Sing r) ->
           (~>:~:) @t @a @(WhySymSym1 a) @b @r singEq Refl

hsym :: forall j k (a :: j) (b :: k).
        a :~~: b -> b :~~: a
hsym eq = withSomeSing eq $ \(singEq :: Sing r) ->
            (~>:~~:) @j @a @(WhyHsymSym1 a) @k @b @r singEq HRefl

symIdempotent :: forall t (a :: t) (b :: t)
                        (e :: a :~: b).
                 Sing e -> Symmetry (Symmetry e) :~: e
symIdempotent se = (~>:~:) @t @a @(WhySymIdempotentSym1 a) @b @e se Refl

hsymIdempotent :: forall j k (a :: j) (b :: k)
                         (e :: a :~~: b).
                  Sing e -> Hsymmetry (Hsymmetry e) :~: e
hsymIdempotent se = (~>:~~:) @j @a @(WhyHsymIdempotentSym1 a) @k @b @e se Refl

replace :: forall t (from :: t) (to :: t) (p :: t ~> Type).
           p @@ from
        -> from :~: to
        -> p @@ to
replace from eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @t @from @(WhyReplaceSym2 from p) @to @r singEq from

-- Doesn't work due to https://ghc.haskell.org/trac/ghc/ticket/11719
{-
hreplace :: forall j k (from :: j) (to :: k)
                   (p :: forall z. z ~> Type).
            p @@ from
         -> from :~~: to
         -> p @@ to
hreplace from heq =
  withSomeSing heq $ \(singEq :: Sing r) ->
    (~>:~~:) @j @from @(WhyHreplaceSym2 from p) @k @to @r singEq from
-}

leibniz :: forall t (f :: t ~> Type) (a :: t) (b :: t).
           a :~: b
        -> f @@ a
        -> f @@ b
leibniz = replace @t @a @b @(WhyLeibnizSym2 f a) id

cong :: forall x y (f :: x ~> y)
               (a :: x) (b :: x).
        a :~: b
     -> f @@ a :~: f @@ b
cong eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @x @a @(WhyCongSym2 f a) @b @r singEq Refl

eqIsRefl :: forall k (a :: k) (b :: k) (e :: a :~: b).
            Sing e -> e :~~: (Refl :: a :~: a)
eqIsRefl eq = (~>:~:) @k @a @(WhyEqIsReflSym1 a) @b @e eq HRefl

heqIsHRefl :: forall j k (a :: j) (b :: k) (e :: a :~~: b).
              Sing e -> e :~~: (HRefl :: a :~~: a)
heqIsHRefl heq = (~>:~~:) @j @a @(WhyHEqIsHReflSym1 a) @k @b @e heq HRefl
