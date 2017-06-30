{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module PeanoSpec where

import Data.Eliminator
import Data.Kind
import Data.Singletons

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

data Peano = Z | S Peano

data instance Sing (z :: Peano) where
  SZ :: Sing Z
  SS :: Sing p -> Sing (S p)

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


