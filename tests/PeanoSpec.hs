{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module PeanoSpec where

import Data.Eliminator
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

elimPeano :: forall (n :: Peano) (p :: Peano -> Type).
             Sing n
          -> p Z
          -> (forall (k :: Peano). Sing k -> p k -> p (S k))
          -> p n
elimPeano = elimPeanoPoly @(:->) @n @p

elimPeanoTyFun :: forall (n :: Peano) (p :: Peano ~> Type).
                  Sing n
               -> p @@ Z
               -> (forall (k :: Peano). Sing k -> p @@ k -> p @@ (S k))
               -> p @@ n
elimPeanoTyFun = elimPeanoPoly @(:~>) @n @p

elimPeanoPoly :: forall (arr :: FunArrow) (n :: Peano) (p :: (Peano -?> Type) arr).
                 FunApp arr
              => Sing n
              -> App Peano arr Type p Z
              -> (forall (k :: Peano). Sing k -> App Peano arr Type p k
                                              -> App Peano arr Type p (S k))
              -> App Peano arr Type p n
elimPeanoPoly SZ pZ _ = pZ
elimPeanoPoly (SS (sk :: Sing k)) pZ pS = pS sk (elimPeanoPoly @arr @k @p sk pZ pS)

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
