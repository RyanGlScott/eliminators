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
      replicateVec (SS SZ) () `shouldBe` VCons () VNil
  describe "mapVec" $ do
    it "maps over a Vec" $ do
      mapVec reverse ("hello" `VCons` "world" `VCons` VNil)
        `shouldBe` ("olleh" `VCons` "dlrow" `VCons` VNil)
  describe "zipWithVec" $ do
    it "zips two Vecs" $ do
      zipWithVec (,) ((2 :: Int) `VCons` 22 `VCons` VNil)
                     ("chicken-of-the-woods" `VCons` "hen-of-woods" `VCons` VNil)
        `shouldBe` ((2, "chicken-of-the-woods") `VCons` (22, "hen-of-woods")
                                                `VCons` VNil)
  describe "appendVec" $ do
    it "appends two Vecs" $ do
      appendVec ("portabello" `VCons` "bay-bolete"
                              `VCons` "funnel-chantrelle"
                              `VCons` VNil)
                ("sheathed-woodtuft" `VCons` "puffball" `VCons` VNil)
        `shouldBe` ("portabello" `VCons` "bay-bolete"
                                 `VCons` "funnel-chantrelle"
                                 `VCons` "sheathed-woodtuft"
                                 `VCons` "puffball"
                                 `VCons` VNil)
  describe "transposeVec" $ do
    it "transposes a Vec" $ do
      transposeVec (('a' `VCons` 'b' `VCons` 'c' `VCons` VNil)
            `VCons` ('d' `VCons` 'e' `VCons` 'f' `VCons` VNil)
            `VCons` VNil)
        `shouldBe`
                   (('a' `VCons` 'd' `VCons` VNil)
            `VCons` ('b' `VCons` 'e' `VCons` VNil)
            `VCons` ('c' `VCons` 'f' `VCons` VNil)
            `VCons` VNil)

-----

replicateVec :: forall (e :: Type) (howMany :: Peano).
                Sing howMany -> e -> Vec e howMany
replicateVec s e = elimPeano @howMany @(Vec e) s VNil step
  where
    step :: forall (k :: Peano). Sing k -> Vec e k -> Vec e (S k)
    step _ = VCons e

mapVec :: forall (a :: Type) (b :: Type) (n :: Peano).
          SingI n
       => (a -> b) -> Vec a n -> Vec b n
mapVec f = elimPeanoTyFun @n @(WhyMapVecSym2 a b) (sing @_ @n) base step
  where
    base :: WhyMapVec a b Z
    base _ = VNil

    step :: forall (k :: Peano). Sing k -> WhyMapVec a b k -> WhyMapVec a b (S k)
    step _ mapK vK = VCons (f (vhead vK)) (mapK (vtail vK))

zipWithVec :: forall (a :: Type) (b :: Type) (c :: Type) (n :: Peano).
              SingI n
           => (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWithVec f = elimPeanoTyFun @n @(WhyZipWithVecSym3 a b c) (sing @_ @n) base step
  where
    base :: WhyZipWithVec a b c Z
    base _ _ = VNil

    step :: forall (k :: Peano).
            Sing k
         -> WhyZipWithVec a b c k
         -> WhyZipWithVec a b c (S k)
    step _ zwK vaK vbK = VCons (f   (vhead vaK) (vhead vbK))
                               (zwK (vtail vaK) (vtail vbK))

appendVec :: forall (e :: Type) (n :: Peano) (m :: Peano).
             SingI n
          => Vec e n -> Vec e m -> Vec e (Plus n m)
appendVec = elimPeanoTyFun @n @(WhyAppendVecSym2 e m) (sing @_ @n) base step
  where
    base :: WhyAppendVec e m Z
    base _ = id

    step :: forall (k :: Peano).
            Sing k
         -> WhyAppendVec e m k
         -> WhyAppendVec e m (S k)
    step _ avK vK1 vK2 = VCons (vhead vK1) (avK (vtail vK1) vK2)

transposeVec :: forall (e :: Type) (n :: Peano) (m :: Peano).
                (SingI n, SingI m)
             => Vec (Vec e m) n -> Vec (Vec e n) m
transposeVec = elimPeanoTyFun @n @(WhyTransposeVecSym2 e m) (sing @_ @n) base step
  where
    base :: WhyTransposeVec e m Z
    base _ = replicateVec (sing @_ @m) VNil

    step :: forall (k :: Peano).
            Sing k
         -> WhyTransposeVec e m k
         -> WhyTransposeVec e m (S k)
    step _ transK vK = zipWithVec VCons (vhead vK) (transK (vtail vK))
