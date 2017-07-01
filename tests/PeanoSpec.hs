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
    it "does what you'd expect" $ do
      mapVec reverse ("hello" `VCons` "world" `VCons` VNil)
        `shouldBe` ("olleh" `VCons` "dlrow" `VCons` VNil)

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
    step _ mapS vS = VCons (f (vhead vS)) (mapS (vtail vS))
