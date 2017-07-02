{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
module VecSpec where

import Data.Kind
import Data.Singletons

import PeanoSpec (appendVec)
import PeanoTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  describe "concatVec" $ do
    it "concats a Vec of Vecs" $ do
      concatVec ((False `VCons` True  `VCons` False `VCons` VNil)
         `VCons` (True  `VCons` False `VCons` True  `VCons` VNil)
         `VCons` VNil)
        `shouldBe` (False `VCons` True  `VCons` False `VCons` True
                          `VCons` False `VCons` True  `VCons` VNil)

-----

concatVec :: forall (e :: Type) (n :: Peano) (j :: Peano).
             (SingKind e, SingI j, e ~ Demote e)
          => Vec (Vec e j) n -> Vec e (Times n j)
concatVec l = withSomeSing l $ \(singL :: Sing l) ->
                elimVecTyFun @(Vec e j) @n @(WhyConcatVecSym e j) @l singL base step
  where
    base :: WhyConcatVec e j Z VNil
    base = VNil

    step :: forall (k :: Peano) (x :: Vec e j) (xs :: Vec (Vec e j) k).
                   Sing x -> Sing xs
                -> WhyConcatVec e j k     xs
                -> WhyConcatVec e j (S k) (VCons x xs)
    step h _ vKJ = appendVec (fromSing h) vKJ
