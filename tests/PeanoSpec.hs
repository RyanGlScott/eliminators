{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
module PeanoSpec where

import Data.Kind
import Data.Singletons

import PeanoTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  describe "replicateVec" $ do
    it "works with empty lists" $
      replicateVec SZ () `shouldBe` VNil
    it "works with non-empty lists" $
      replicateVec (SS SZ) () `shouldBe` () :# VNil
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

-----

replicateVec :: forall (e :: Type) (howMany :: Peano).
                Sing howMany -> e -> Vec e howMany
replicateVec s e = elimPeano @howMany @(TyCon1 (Vec e)) s VNil step
  where
    step :: forall (k :: Peano). Sing k -> Vec e k -> Vec e (S k)
    step _ = (e :#)

mapVec :: forall (a :: Type) (b :: Type) (n :: Peano).
          SingI n
       => (a -> b) -> Vec a n -> Vec b n
mapVec f = elimPeano @n @(WhyMapVecSym2 a b) (sing @_ @n) base step
  where
    base :: WhyMapVec a b Z
    base _ = VNil

    step :: forall (k :: Peano). Sing k -> WhyMapVec a b k -> WhyMapVec a b (S k)
    step _ mapK vK = f (vhead vK) :# mapK (vtail vK)

zipWithVec :: forall (a :: Type) (b :: Type) (c :: Type) (n :: Peano).
              SingI n
           => (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWithVec f = elimPeano @n @(WhyZipWithVecSym3 a b c) (sing @_ @n) base step
  where
    base :: WhyZipWithVec a b c Z
    base _ _ = VNil

    step :: forall (k :: Peano).
            Sing k
         -> WhyZipWithVec a b c k
         -> WhyZipWithVec a b c (S k)
    step _ zwK vaK vbK = f   (vhead vaK) (vhead vbK)
                      :# zwK (vtail vaK) (vtail vbK)

appendVec :: forall (e :: Type) (n :: Peano) (m :: Peano).
             SingI n
          => Vec e n -> Vec e m -> Vec e (Plus n m)
appendVec = elimPeano @n @(WhyAppendVecSym2 e m) (sing @_ @n) base step
  where
    base :: WhyAppendVec e m Z
    base _ = id

    step :: forall (k :: Peano).
            Sing k
         -> WhyAppendVec e m k
         -> WhyAppendVec e m (S k)
    step _ avK vK1 vK2 = vhead vK1 :# avK (vtail vK1) vK2

transposeVec :: forall (e :: Type) (n :: Peano) (m :: Peano).
                (SingI n, SingI m)
             => Vec (Vec e m) n -> Vec (Vec e n) m
transposeVec = elimPeano @n @(WhyTransposeVecSym2 e m) (sing @_ @n) base step
  where
    base :: WhyTransposeVec e m Z
    base _ = replicateVec (sing @_ @m) VNil

    step :: forall (k :: Peano).
            Sing k
         -> WhyTransposeVec e m k
         -> WhyTransposeVec e m (S k)
    step _ transK vK = zipWithVec (:#) (vhead vK) (transK (vtail vK))
