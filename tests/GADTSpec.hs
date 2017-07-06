{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module GADTSpec where

import Data.Eliminator
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

elimSo :: forall (what :: Bool) (s :: So what) (p :: forall (long_sucker :: Bool). So long_sucker -> Type).
          Sing s
       -> p Oh
       -> p s
elimSo SOh pOh = pOh

elimSoTyFun :: forall (what :: Bool) (s :: So what) (p :: forall (long_sucker :: Bool). So long_sucker ~> Type).
               Sing s
            -> p @@ Oh
            -> p @@ s
elimSoTyFun SOh pOh = pOh

{-
I don't know how to make this kind-check :(
elimSoPoly :: forall (arr :: FunArrow) (what :: Bool) (s :: So what)
                     (p :: forall (long_sucker :: Bool). (So long_sucker -?> Type) arr).
              Sing s
           -> App (So True) arr Type p Oh
           -> App (So what) arr Type p s
elimSoPoly SOh pOh = pOh
-}

data Flarble (a :: Type) (b :: Type) where
  MkFlarble1 :: a -> Flarble a b
  MkFlarble2 :: a ~ Bool => Flarble a (Maybe b)

data instance Sing (z :: Flarble a b) where
  SMkFlarble1 :: Sing x -> Sing (MkFlarble1 x)
  SMkFlarble2 :: Sing MkFlarble2

elimFlarble :: forall (a :: Type) (b :: Type)
                      (p :: forall (x :: Type) (y :: Type). Flarble x y -> Type)
                      (f :: Flarble a b).
               Sing f
            -> (forall (x :: a). Sing x -> p (MkFlarble1 x :: Flarble a b))
            -> (forall (b' :: Type). p (MkFlarble2 :: Flarble Bool (Maybe b')))
            -> p f
elimFlarble s@(SMkFlarble1 sx) pMkFlarble1 _ =
  case s of
    (_ :: Sing (MkFlarble1 x :: Flarble a b)) -> pMkFlarble1 @x sx
elimFlarble s@SMkFlarble2 _ pMkFlarble2 =
  case s of
    (_ :: Sing (MkFlarble2 :: Flarble Bool (Maybe b'))) -> pMkFlarble2 @b'

elimFlarbleTyFun :: forall (a :: Type) (b :: Type)
                           (p :: forall (x :: Type) (y :: Type). Flarble x y ~> Type)
                           (f :: Flarble a b).
                    Sing f
                 -> (forall (x :: a). Sing x -> p @@ (MkFlarble1 x :: Flarble a b))
                 -> (forall (b' :: Type). p @@ (MkFlarble2 :: Flarble Bool (Maybe b')))
                 -> p @@ f
elimFlarbleTyFun s@(SMkFlarble1 sx) pMkFlarble1 _ =
  case s of
    (_ :: Sing (MkFlarble1 x :: Flarble a b)) -> pMkFlarble1 @x sx
elimFlarbleTyFun s@SMkFlarble2 _ pMkFlarble2 =
  case s of
    (_ :: Sing (MkFlarble2 :: Flarble Bool (Maybe b'))) -> pMkFlarble2 @b'

data Obj :: Type where
  MkObj :: o -> Obj

data instance Sing (z :: Obj) where
  SMkObj :: forall (obj :: obiwan). Sing obj -> Sing (MkObj obj)

elimObj :: forall (o :: Obj) (p :: Obj -> Type).
           Sing o
        -> (forall (obj :: Type) (x :: obj). Sing x -> p (MkObj x))
        -> p o
elimObj = elimObjPoly @(:->) @o @p

elimObjTyFun :: forall (o :: Obj) (p :: Obj ~> Type).
                Sing o
             -> (forall (obj :: Type) (x :: obj). Sing x -> p @@ (MkObj x))
             -> p @@ o
elimObjTyFun = elimObjPoly @(:~>) @o @p

elimObjPoly :: forall (arr :: FunArrow) (o :: Obj) (p :: (Obj -?> Type) arr).
               Sing o
            -> (forall (obj :: Type) (x :: obj). Sing x -> App Obj arr Type p (MkObj x))
            -> App Obj arr Type p o
elimObjPoly (SMkObj (x :: Sing (obj :: obiwan))) pMkObj = pMkObj @obiwan @obj x
