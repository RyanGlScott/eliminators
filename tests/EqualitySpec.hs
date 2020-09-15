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
{-# LANGUAGE UnsaturatedTypeFamilies #-}
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
spec = pure ()
{-
spec = parallel $ do
  describe "sym" $ do
    let boolEq :: Bool :~: Bool
        boolEq = Refl
    it "behaves like the one from Data.Type.Equality" $ do
      sym boolEq       `shouldBe` DTE.sym boolEq
      sym (sym boolEq) `shouldBe` DTE.sym (DTE.sym boolEq)
    it "behaves like the one from Data.Type.Equality" $ do
      trans boolEq boolEq       `shouldBe` DTE.trans boolEq boolEq
      trans boolEq (sym boolEq) `shouldBe` Refl
-}

-----

j :: forall {m} k (p :: forall (x :: k) (y :: k). x :~: y -> @m Type)
            (a :: k) (b :: k)
            (r :: a :~: b).
     Sing r
  -> (forall (x :: k). p (Refl @x))
  -> p r
j SRefl pRefl = pRefl @a

jProp :: forall {m} {n} k (p :: k -> @m k -> @n Prop)
                (a :: k) (b :: k).
         a :~: b
      -> (forall (x :: k). p x x)
      -> p a b
jProp Refl pRefl = pRefl @a

hj :: forall {m} (p :: forall y z (w :: y) (x :: z). w :~~: x -> @m Type)
             j k (a :: j) (b :: k)
             (r :: a :~~: b).
      Sing r
   -> (forall y (w :: y). p (HRefl @w))
   -> p r
hj SHRefl pHRefl = pHRefl @j @a

hjProp :: forall {m} {n} (p :: forall y z. y -> @m z -> @n Prop)
                 j k (a :: j) (b :: k).
          a :~~: b
       -> (forall y (w :: y). p w w)
       -> p a b
hjProp HRefl pHRefl = pHRefl @j @a

k :: forall {m} k (a :: k)
            (p :: a :~: a -> @m Type)
            (r :: a :~: a).
     Sing r
  -> p Refl
  -> p r
k SRefl pRefl = pRefl

hk :: forall {m} k (a :: k)
             (p :: a :~~: a -> @m Type)
             (r :: a :~~: a).
      Sing r
   -> p HRefl
   -> p r
hk SHRefl pHRefl = pHRefl

{-
sym :: forall t (a :: t) (b :: t).
       a :~: b -> b :~: a
sym eq = withSomeSing eq $ \(singEq :: Sing r) ->
           (~>:~:) @t @a @WhySym @b @r singEq Refl

sSym :: forall t (a :: t) (b :: t) (e :: a :~: b).
        Sing e -> Sing (Symmetry e)
sSym se = (~>:~:) @t @a @WhySSym @b @e se SRefl

hsym :: forall j k (a :: j) (b :: k).
        a :~~: b -> b :~~: a
hsym eq = withSomeSing eq $ \(singEq :: Sing r) ->
            (~>:~~:) @j @a @WhyHSym @k @b @r singEq HRefl

sHSym :: forall j k (a :: j) (b :: k) (e :: a :~~: b).
         Sing e -> Sing (HSymmetry e)
sHSym se = (~>:~~:) @j @a @WhySHSym @k @b @e se SHRefl

symIdempotent :: forall t (a :: t) (b :: t)
                        (e :: a :~: b).
                 Sing e -> Symmetry (Symmetry e) :~: e
symIdempotent se = (~>:~:) @t @a @WhySymIdempotent @b @e se Refl

hsymIdempotent :: forall j k (a :: j) (b :: k)
                         (e :: a :~~: b).
                  Sing e -> HSymmetry (HSymmetry e) :~: e
hsymIdempotent se = (~>:~~:) @j @a @WhyHSymIdempotent @k @b @e se Refl

trans :: forall t (a :: t) (b :: t) (c :: t).
                a :~: b -> b :~: c -> a :~: c
trans eq1 eq2 = withSomeSing eq1 $ \(singEq1 :: Sing r) ->
                  unwrapTrans ((~>:~:) @t @a @WrappedTrans @b @r
                                       singEq1 (WrapTrans id)) eq2

htrans :: forall j k l (a :: j) (b :: k) (c :: l).
                 a :~~: b -> b :~~: c -> a :~~: c
htrans eq1 eq2 = withSomeSing eq1 $ \(singEq1 :: Sing r) ->
                   unwrapHTrans ((~>:~~:) @j @a @WrappedHTrans @k @b @r
                                          singEq1 (WrapHTrans id)) eq2

replace :: forall {m} t (from :: t) (to :: t) (p :: t -> @m Type).
           p from
        -> from :~: to
        -> p to
replace from eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @t @from @(WhyReplace from p) @to @r singEq from

hreplace :: forall {m} j k (from :: j) (to :: k)
                   (p :: forall z. z -> @m Type).
            p from
         -> from :~~: to
         -> p to
hreplace from heq =
  withSomeSing heq $ \(singEq :: Sing r) ->
    (~>:~~:) @j @from @(WhyHReplace from (WrapPred p)) @k @to @r singEq from

leibniz :: forall {m} t (f :: t -> @m Type) (a :: t) (b :: t).
           a :~: b
        -> f a
        -> f b
leibniz = replace @t @a @b @(WhyLeibniz f a) id

hleibniz :: forall {m} (f :: forall t. t -> @m Type) j k (a :: j) (b :: k).
            a :~~: b
         -> f a
         -> f b
hleibniz = hreplace @j @k @a @b @(WhyHLeibniz (WrapPred f) a) id

cong :: forall {m} x y (f :: x -> @m y)
               (a :: x) (b :: x).
        a :~: b
     -> f a :~: f b
cong eq =
  withSomeSing eq $ \(singEq :: Sing r) ->
    (~>:~:) @x @a @(WhyCong f) @b @r singEq Refl

eqIsRefl :: forall k (a :: k) (b :: k) (e :: a :~: b).
            Sing e -> e :~~: (Refl :: a :~: a)
eqIsRefl eq = (~>:~:) @k @a @WhyEqIsRefl @b @e eq HRefl

heqIsHRefl :: forall j k (a :: j) (b :: k) (e :: a :~~: b).
              Sing e -> e :~~: (HRefl :: a :~~: a)
heqIsHRefl heq = (~>:~~:) @j @a @WhyHEqIsHRefl @k @b @e heq HRefl

transLeft :: forall j (a :: j) (b :: j) (e :: a :~: b).
             Sing e -> Trans e Refl :~: e
transLeft se = leibniz @(a :~: b) @WhyTransLeft
                       @(Symmetry (Symmetry e)) @e
                       (symIdempotent se) transLeftHelper
  where
    transLeftHelper :: Trans (Symmetry (Symmetry e)) Refl
                   :~: Symmetry (Symmetry e)
    transLeftHelper = (~>:~:) @j @b @WhyTransLeftHelper @a @(Symmetry e)
                              (sSym se) Refl

htransLeft :: forall j k (a :: j) (b :: k) (e :: a :~~: b).
              Sing e -> HTrans e HRefl :~: e
htransLeft se = leibniz @(a :~~: b) @WhyHTransLeft
                        @(HSymmetry (HSymmetry e)) @e
                        (hsymIdempotent se) htransLeftHelper
  where
    htransLeftHelper :: HTrans (HSymmetry (HSymmetry e)) HRefl
                    :~: HSymmetry (HSymmetry e)
    htransLeftHelper = (~>:~~:) @k @b @WhyHTransLeftHelper @j @a @(HSymmetry e)
                                (sHSym se) Refl

transRight :: forall j (a :: j) (b :: j) (e :: a :~: b).
              Sing e -> Trans Refl e :~: e
transRight se = (~>:~:) @j @a @WhyTransRight @b @e se Refl

htransRight :: forall j k (a :: j) (b :: k) (e :: a :~~: b).
               Sing e -> HTrans HRefl e :~: e
htransRight se = (~>:~~:) @j @a @WhyHTransRight @k @b @e se Refl

-- Commented out for now, since these take ages to compile :(
-- Perhaps https://gitlab.haskell.org/ghc/ghc/merge_requests/611 will make
-- things tolerable.
{-
sTrans :: forall t (a :: t) (b :: t) (c :: t)
                   (e1 :: a :~: b) (e2 :: b :~: c).
          Sing e1 -> Sing e2 -> Sing (Trans e1 e2)
sTrans se1 = unwrapSTrans $ (~>:~:) @t @a @WhySTrans @b @e1
                                    se1 (WrapSTrans sTransHelper)
  where
    sTransHelper :: forall (z :: t) (e' :: a :~: z).
                    Sing e' -> Sing (Trans Refl e')
    sTransHelper se' = leibniz @(a :~: z) @(TyCon1 Sing) @e' @(Trans Refl e')
                               (sym (transRight se')) se'

sHTrans :: forall j k l (a :: j) (b :: k) (c :: l)
                  (e1 :: a :~~: b) (e2 :: b :~~: c).
           Sing e1 -> Sing e2 -> Sing (HTrans e1 e2)
sHTrans se1 = unwrapSHTrans $ (~>:~~:) @j @a @WhySHTrans @k @b @e1
                                       se1 (WrapSHTrans sHTransHelper)
  where
    sHTransHelper :: forall m (z :: m) (e' :: a :~~: z).
                     Sing e' -> Sing (HTrans HRefl e')
    sHTransHelper se' = leibniz @(a :~~: z) @(TyCon1 Sing) @e' @(HTrans HRefl e')
                                (sym (htransRight se')) se'

rebalance :: forall j (x1 :: j) (x2 :: j) (x3 :: j) (x4 :: j)
                    (a :: x1 :~: x2) (b :: x2 :~: x3) (c :: x3 :~: x4).
             Sing a -> Sing b -> Sing c
          -> Trans a (Trans b c) :~: Trans (Trans a b) c
rebalance sa sb sc = leibniz @(x1 :~: x2) @(WhyRebalance b c)
                             @(Symmetry (Symmetry a)) @a
                             (symIdempotent sa) rebalanceHelper
  where
    rebalanceHelper :: Trans (Symmetry (Symmetry a)) (Trans b c)
                   :~: Trans (Trans (Symmetry (Symmetry a)) b) c
    rebalanceHelper = (~>:~:) @j @x2 @(WhyRebalanceHelper b c) @x1 @(Symmetry a)
                              (sSym sa) rebalanceBC

    rebalanceBC :: Trans Refl (Trans b c) :~: Trans (Trans Refl b) c
    rebalanceBC = trans (transRight (sTrans sb sc)) transRightBC

    transRightBC :: Trans b c :~: Trans (Trans Refl b) c
    transRightBC = cong @(x2 :~: x3) @(x2 :~: x4) @(Flip Trans c)
                        @b @(Trans Refl b)
                        (sym (transRight sb))

hrebalance :: forall k1 k2 k3 k4 (x1 :: k1) (x2 :: k2) (x3 :: k3) (x4 :: k4)
                     (a :: x1 :~~: x2) (b :: x2 :~~: x3) (c :: x3 :~~: x4).
              Sing a -> Sing b -> Sing c
           -> HTrans a (HTrans b c) :~: HTrans (HTrans a b) c
hrebalance sa sb sc = leibniz @(x1 :~~: x2) @(WhyHRebalance b c)
                              @(HSymmetry (HSymmetry a)) @a
                              (hsymIdempotent sa) hrebalanceHelper
  where
    hrebalanceHelper :: HTrans (HSymmetry (HSymmetry a)) (HTrans b c)
                    :~: HTrans (HTrans (HSymmetry (HSymmetry a)) b) c
    hrebalanceHelper = (~>:~~:) @k2 @x2 @(WhyHRebalanceHelper b c)
                                @k1 @x1 @(HSymmetry a)
                                (sHSym sa) hrebalanceBC

    hrebalanceBC :: HTrans HRefl (HTrans b c) :~: HTrans (HTrans HRefl b) c
    hrebalanceBC = trans (htransRight (sHTrans sb sc)) htransRightBC

    htransRightBC :: HTrans b c :~: HTrans (HTrans HRefl b) c
    htransRightBC = cong @(x2 :~~: x3) @(x2 :~~: x4) @(Flip HTrans c)
                         @b @(HTrans HRefl b)
                         (sym (htransRight sb))
-}
-}
