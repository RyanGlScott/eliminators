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

import Internal

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

data So :: Bool -> Type where
  Oh :: So True

data instance Sing :: forall (what :: Bool). So what -> Type where
  SOh :: Sing Oh
type SSo = (Sing :: So what -> Type)

elimSo :: forall (p :: forall (long_sucker :: Bool). So long_sucker ~> Type)
                 (what :: Bool) (s :: So what).
          Sing s
       -> p @@ Oh
       -> p @@ s
elimSo SOh pOh = pOh

elimPropSo :: forall (p :: Bool ~> Prop) (what :: Bool).
              So what
           -> p @@ True
           -> p @@ what
elimPropSo Oh pOh = pOh

data Flarble :: Type -> Type -> Type where
  MkFlarble1 :: a -> Flarble a b
  MkFlarble2 :: a ~ Bool => Flarble a (Maybe b)

data instance Sing :: forall a b. Flarble a b -> Type where
  SMkFlarble1 :: Sing x -> Sing (MkFlarble1 x)
  SMkFlarble2 :: Sing MkFlarble2
type SFlarble = (Sing :: Flarble a b -> Type)

elimFlarble :: forall (p :: forall x y. Flarble x y ~> Type)
                      a b (f :: Flarble a b).
               Sing f
            -> (forall a' b' (x :: a'). Sing x -> p @@ (MkFlarble1 x :: Flarble a' b'))
            -> (forall b'. p @@ (MkFlarble2 :: Flarble Bool (Maybe b')))
            -> p @@ f
elimFlarble s@(SMkFlarble1 sx) pMkFlarble1 _ =
  case s of
    (_ :: Sing (MkFlarble1 x :: Flarble a' b')) -> pMkFlarble1 @a' @b' @x sx
elimFlarble s@SMkFlarble2 _ pMkFlarble2 =
  case s of
    (_ :: Sing (MkFlarble2 :: Flarble Bool (Maybe b'))) -> pMkFlarble2 @b'

elimPropFlarble :: forall (p :: Type ~> Type ~> Prop) a b.
                   Flarble a b
                -> (forall a' b'. a -> p @@ a' @@ b')
                -> (forall b'. p @@ Bool @@ Maybe b')
                -> p @@ a @@ b
elimPropFlarble f@(MkFlarble1 x) pMkFlarble1 _ =
  case f of
    (_ :: Flarble a' b') -> pMkFlarble1 @a' @b' x
elimPropFlarble f@MkFlarble2 _ pMkFlarble2 =
  case f of
    (_ :: Flarble Bool (Maybe b')) -> pMkFlarble2 @b'

data Obj :: Type where
  MkObj :: o -> Obj

data instance Sing :: Obj -> Type where
  SMkObj :: forall obiwan (obj :: obiwan). Sing obj -> Sing (MkObj obj)
type SObj = (Sing :: Obj -> Type)

elimObj :: forall (p :: Obj ~> Type) (o :: Obj).
           Sing o
        -> (forall obj (x :: obj). Sing x -> p @@ MkObj x)
        -> p @@ o
elimObj (SMkObj (sx :: Sing (x :: obj))) pMkObj = pMkObj @obj @x sx

elimPropObj :: forall (p :: Prop).
               Obj
            -> (forall obj. obj -> p)
            -> p
elimPropObj (MkObj o) pMkObj = pMkObj o
