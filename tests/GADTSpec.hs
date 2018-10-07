{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module GADTSpec where

import Data.Kind
import Data.Singletons

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

data So :: Bool -> Type where
  Oh :: So True

data instance Sing (z :: So what) where
  SOh :: Sing Oh
type SSo = (Sing :: So what -> Type)

elimSo :: forall (what :: Bool) (s :: So what) (p :: forall (long_sucker :: Bool). So long_sucker ~> Type).
          Sing s
       -> p @@ Oh
       -> p @@ s
elimSo SOh pOh = pOh

data Flarble (a :: Type) (b :: Type) where
  MkFlarble1 :: a -> Flarble a b
  MkFlarble2 :: a ~ Bool => Flarble a (Maybe b)

data instance Sing (z :: Flarble a b) where
  SMkFlarble1 :: Sing x -> Sing (MkFlarble1 x)
  SMkFlarble2 :: Sing MkFlarble2
type SFlarble = (Sing :: Flarble a b -> Type)

elimFlarble :: forall (a :: Type) (b :: Type)
                      (p :: forall (x :: Type) (y :: Type). Flarble x y ~> Type)
                      (f :: Flarble a b).
               Sing f
            -> (forall (a' :: Type) (b' :: Type) (x :: a'). Sing x -> p @@ (MkFlarble1 x :: Flarble a' b'))
            -> (forall (b' :: Type). p @@ (MkFlarble2 :: Flarble Bool (Maybe b')))
            -> p @@ f
elimFlarble s@(SMkFlarble1 sx) pMkFlarble1 _ =
  case s of
    (_ :: Sing (MkFlarble1 x :: Flarble a' b')) -> pMkFlarble1 @a' @b' @x sx
elimFlarble s@SMkFlarble2 _ pMkFlarble2 =
  case s of
    (_ :: Sing (MkFlarble2 :: Flarble Bool (Maybe b'))) -> pMkFlarble2 @b'

data Obj :: Type where
  MkObj :: o -> Obj

data instance Sing (z :: Obj) where
  SMkObj :: forall obiwan (obj :: obiwan). Sing obj -> Sing (MkObj obj)
type SObj = (Sing :: Obj -> Type)

elimObj :: forall (o :: Obj) (p :: Obj ~> Type).
           Sing o
        -> (forall (obj :: Type) (x :: obj). Sing x -> p @@ (MkObj x))
        -> p @@ o
elimObj (SMkObj (x :: Sing (obj :: obiwan))) pMkObj = pMkObj @obiwan @obj x
