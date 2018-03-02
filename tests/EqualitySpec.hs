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

j :: forall (k :: Type) (a :: k) (b :: k)
            (p :: forall (x :: k) (y :: k). x :~: y ~> Type)
            (r :: a :~: b).
     Sing r
  -> (forall (x :: k). p @@ (Refl :: x :~: x))
  -> p @@ r
j SRefl pRefl = pRefl @a

hj :: forall (j :: Type) (k :: Type) (a :: j) (b :: k)
             (p :: forall (y :: Type) (z :: Type) (w :: y) (x :: z). w :~~: x ~> Type)
             (r :: a :~~: b).
      Sing r
   -> (forall (y :: Type) (w :: y). p @@ (HRefl :: w :~~: w))
   -> p @@ r
hj SHRefl pHRefl = pHRefl @k @a

k :: forall (k :: Type) (a :: k)
            (p :: a :~: a ~> Type)
            (r :: a :~: a).
     Sing r
  -> p @@ Refl
  -> p @@ r
k SRefl pRefl = pRefl

hk :: forall (k :: Type) (a :: k)
             (p :: a :~~: a ~> Type)
             (r :: a :~~: a).
      Sing r
   -> p @@ HRefl
   -> p @@ r
hk SHRefl pHRefl = pHRefl

sym :: forall (t :: Type) (a :: t) (b :: t).
       a :~: b -> b :~: a
sym eq = withSomeSing eq $ \(singEq :: Sing r) ->
           (~>:~:) @t @a @b @(WhySymSym1 a) @r singEq Refl

hsym :: forall (j :: Type) (k :: Type) (a :: j) (b :: k).
        a :~~: b -> b :~~: a
hsym eq = withSomeSing eq $ \(singEq :: Sing r) ->
            (~>:~~:) @j @k @a @b @(WhyHsymSym1 a) @r singEq HRefl

symIdempotent :: forall (t :: Type) (a :: t) (b :: t)
                        (e :: a :~: b).
                 Sing e -> Symmetry (Symmetry e) :~: e
symIdempotent se = (~>:~:) @t @a @b @(WhySymIdempotentSym1 a) @e se Refl

hsymIdempotent :: forall (j :: Type) (k :: Type) (a :: j) (b :: k)
                         (e :: a :~~: b).
                  Sing e -> Hsymmetry (Hsymmetry e) :~: e
hsymIdempotent se = (~>:~~:) @j @k @a @b @(WhyHsymIdempotentSym1 a) @e se Refl

replace :: forall (t :: Type) (from :: t) (to :: t) (p :: t ~> Type).
           p @@ from
        -> from :~: to
        -> p @@ to
replace from eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @t @from @to @(WhyReplaceSym2 from p) @r singEq from

-- Doesn't work due to https://ghc.haskell.org/trac/ghc/ticket/11719
{-
hreplace :: forall (j :: Type) (k :: Type) (from :: j) (to :: k)
                   (p :: forall (z :: Type). z ~> Type).
            p @@ from
         -> from :~~: to
         -> p @@ to
hreplace from heq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (@~>:~~:) @j @k @from @to @(WhyHreplaceSym2 from p) singEq from
-}

leibniz :: forall (t :: Type) (f :: t ~> Type) (a :: t) (b :: t).
           a :~: b
        -> f @@ a
        -> f @@ b
leibniz = replace @t @a @b @(WhyLeibnizSym2 f a) id

cong :: forall (x :: Type) (y :: Type) (f :: x ~> y)
               (a :: x) (b :: x).
        a :~: b
     -> f @@ a :~: f @@ b
cong eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @x @a @b @(WhyCongSym2 f a) @r singEq Refl

eqIsRefl :: forall (k :: Type) (a :: k) (b :: k) (e :: a :~: b).
            Sing e -> e :~~: (Refl :: a :~: a)
eqIsRefl eq = (~>:~:) @k @a @b @(WhyEqIsReflSym1 a) @e eq HRefl

heqIsHRefl :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (e :: a :~~: b).
              Sing e -> e :~~: (HRefl :: a :~~: a)
heqIsHRefl heq = (~>:~~:) @j @k @a @b @(WhyHEqIsHReflSym1 a) @e heq HRefl
