{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module VecSpec where

import Data.Eliminator
import Data.Nat
import Data.Singletons
import Data.Singletons.Prelude.Num

import VecTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  describe "replicateVec" $ do
    it "works with empty lists" $
      replicateVec (sLit @0) () `shouldBe` VNil
    it "works with non-empty lists" $ do
      replicateVec (sLit @1) () `shouldBe` () :# VNil
      replicateVec (sLit @2) () `shouldBe` () :# () :# VNil
  describe "mapVec" $ do
    it "maps over a Vec" $ do
      mapVec reverse ("hello" :# "world" :# VNil)
          `shouldBe` ("olleh" :# "dlrow" :# VNil)
  describe "zipWithVec" $ do
    it "zips two Vecs" $ do
      zipWithVec (,) ((2 :: Int) :# 22 :# VNil)
                     ("chicken-of-the-woods" :# "hen-of-woods" :# VNil)
        `shouldBe` ((2, "chicken-of-the-woods") :# (22, "hen-of-woods")
                                                :# VNil)
  describe "appendVec" $ do
    it "appends two Vecs" $ do
      appendVec ("portabello" :# "bay-bolete"
                              :# "funnel-chantrelle"
                              :# VNil)
                ("sheathed-woodtuft" :# "puffball" :# VNil)
        `shouldBe` ("portabello" :# "bay-bolete"
                                 :# "funnel-chantrelle"
                                 :# "sheathed-woodtuft"
                                 :# "puffball"
                                 :# VNil)
  describe "transposeVec" $ do
    it "transposes a Vec" $ do
      transposeVec (('a' :# 'b' :# 'c' :# VNil)
                 :# ('d' :# 'e' :# 'f' :# VNil)
                 :# VNil)
        `shouldBe`
                   (('a' :# 'd' :# VNil)
                 :# ('b' :# 'e' :# VNil)
                 :# ('c' :# 'f' :# VNil)
                 :# VNil)
  describe "concatVec" $ do
    it "concats a Vec of Vecs" $ do
      concatVec ((False :# True  :# False :# VNil)
              :# (True  :# False :# True  :# VNil)
              :# VNil)
        `shouldBe` (False :# True  :# False :# True
                          :# False :# True  :# VNil)

-----

replicateVec :: forall e (howMany :: Nat).
                Sing howMany -> e -> Vec e howMany
replicateVec s e = elimNat @(TyCon (Vec e)) @howMany s VNil step
  where
    step :: forall (k :: Nat). Sing k -> Vec e k -> Vec e (S k)
    step _ = (e :#)

mapVec :: forall a b (n :: Nat).
          SingI n
       => (a -> b) -> Vec a n -> Vec b n
mapVec f = elimNat @(WhyMapVecSym2 a b) @n (sing @n) base step
  where
    base :: WhyMapVec a b Z
    base _ = VNil

    step :: forall (k :: Nat). Sing k -> WhyMapVec a b k -> WhyMapVec a b (S k)
    step _ mapK vK = f (vhead vK) :# mapK (vtail vK)

zipWithVec :: forall a b c (n :: Nat).
              SingI n
           => (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWithVec f = elimNat @(WhyZipWithVecSym3 a b c) @n (sing @n) base step
  where
    base :: WhyZipWithVec a b c Z
    base _ _ = VNil

    step :: forall (k :: Nat).
            Sing k
         -> WhyZipWithVec a b c k
         -> WhyZipWithVec a b c (S k)
    step _ zwK vaK vbK = f   (vhead vaK) (vhead vbK)
                      :# zwK (vtail vaK) (vtail vbK)

appendVec :: forall e (n :: Nat) (m :: Nat).
             SingI n
          => Vec e n -> Vec e m -> Vec e (n + m)
appendVec = elimNat @(WhyAppendVecSym2 e m) @n (sing @n) base step
  where
    base :: WhyAppendVec e m Z
    base _ = id

    step :: forall (k :: Nat).
            Sing k
         -> WhyAppendVec e m k
         -> WhyAppendVec e m (S k)
    step _ avK vK1 vK2 = vhead vK1 :# avK (vtail vK1) vK2

transposeVec :: forall e (n :: Nat) (m :: Nat).
                (SingI n, SingI m)
             => Vec (Vec e m) n -> Vec (Vec e n) m
transposeVec = elimNat @(WhyTransposeVecSym2 e m) @n (sing @n) base step
  where
    base :: WhyTransposeVec e m Z
    base _ = replicateVec (sing @m) VNil

    step :: forall (k :: Nat).
            Sing k
         -> WhyTransposeVec e m k
         -> WhyTransposeVec e m (S k)
    step _ transK vK = zipWithVec (:#) (vhead vK) (transK (vtail vK))

concatVec :: forall e (n :: Nat) (j :: Nat).
             (SingKind e, SingI j, e ~ Demote e)
          => Vec (Vec e j) n -> Vec e (n * j)
concatVec l = withSomeSing l $ \(singL :: Sing l) ->
                elimVec @(Vec e j) @n @(WhyConcatVecSym2 e j) @l singL base step
  where
    base :: WhyConcatVec e j VNil
    base = VNil

    step :: forall (k :: Nat) (x :: Vec e j) (xs :: Vec (Vec e j) k).
                   Sing x -> Sing xs
                -> WhyConcatVec e j xs
                -> WhyConcatVec e j (x :# xs)
    step h _ vKJ = appendVec (fromSing h) vKJ
