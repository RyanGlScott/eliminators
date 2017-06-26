{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-|
Module:      Data.Eliminator
Copyright:   (C) 2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Dependently typed elimination functions using @singletons@.
-}
module Data.Eliminator where

import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import Unsafe.Coerce

data FunArrow = (:->) | (:~>)

class FunType (arr :: FunArrow) where
  type Fun (k1 :: Type) arr (k2 :: Type) :: Type

class FunType arr => AppType (arr :: FunArrow) where
  -- Can't be defined in the same class due to staging restrictions
  type App k1 arr k2 (f :: Fun k1 arr k2) (x :: k1) :: k2

type FunApp arr = (FunType arr, AppType arr)

instance FunType (:->) where
  type Fun k1 (:->) k2 = k1 -> k2

instance AppType (:->) where
  type App k1 (:->) k2 (f :: k1 -> k2) x = f x

instance FunType (:~>) where
  type Fun k1 (:~>) k2 = k1 ~> k2

instance AppType (:~>) where
  type App k1 (:~>) k2 (f :: k1 ~> k2) x = f @@ x

infixr 0 -?>
type (-?>) (k1 :: Type) (k2 :: Type) (arr :: FunArrow) = Fun k1 arr k2

boolElim :: forall (p :: Bool -> Type) (b :: Bool).
            Sing b
         -> p False
         -> p True
         -> p b
{-
boolElim SFalse pF _  = pF
boolElim STrue  _  pT = pT
-}
boolElim = boolElimPoly @(:->) @p @b

boolElimTyFun :: forall (p :: Bool ~> Type) (b :: Bool).
                 Sing b
              -> p @@ False
              -> p @@ True
              -> p @@ b
{-
boolElimTyFun SFalse pF _  = pF
boolElimTyFun STrue  _  pT = pT
-}
boolElimTyFun = boolElimPoly @(:~>) @p @b

boolElimPoly :: forall (arr :: FunArrow) (p :: (Bool -?> Type) arr) (b :: Bool).
                FunApp arr
             => Sing b
             -> App Bool arr Type p False
             -> App Bool arr Type p True
             -> App Bool arr Type p b
boolElimPoly SFalse pF _  = pF
boolElimPoly STrue  _  pT = pT

listElim :: forall (a :: Type) (p :: [a] -> Type) (l :: [a]).
            Sing l
         -> p '[]
         -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p xs -> p (x:xs))
         -> p l
{-
listElim SNil                      pNil _     = pNil
listElim (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (listElim @a @p @xs xs pNil pCons)
-}
listElim = listElimPoly @(:->) @a @p @l

listElimTyFun :: forall (a :: Type) (p :: [a] ~> Type) (l :: [a]).
                 Sing l
              -> p @@ '[]
              -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ xs -> p @@ (x:xs))
              -> p @@ l
{-
listElimTyFun SNil                      pNil _     = pNil
listElimTyFun (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (listElimTyFun @a @p @xs xs pNil pCons)
-}
listElimTyFun = listElimPoly @(:~>) @a @p @l

listElimPoly :: forall (arr :: FunArrow) (a :: Type) (p :: ([a] -?> Type) arr) (l :: [a]).
                FunApp arr
             => Sing l
             -> App [a] arr Type p '[]
             -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> App [a] arr Type p xs -> App [a] arr Type p (x:xs))
             -> App [a] arr Type p l
listElimPoly SNil                      pNil _     = pNil
listElimPoly (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (listElimPoly @arr @a @p @xs xs pNil pCons)

natElim :: forall (p :: Nat -> Type) (n :: Nat).
           Sing n
        -> p 0
        -> (forall (k :: Nat). Sing k -> p k -> p (k :+ 1))
        -> p n
{-
natElim snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing (sn :: Sing k) -> unsafeCoerce (pS sn (natElim @p @k sn pZ pS))
-}
natElim = natElimPoly @(:->) @p @n

natElimTyFun :: forall (p :: Nat ~> Type) (n :: Nat).
                Sing n
             -> p @@ 0
             -> (forall (k :: Nat). Sing k -> p @@ k -> p @@ (k :+ 1))
             -> p @@ n
{-
natElimTyFun snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing (sn :: Sing k) -> unsafeCoerce (pS sn (natElimTyFun @p @k sn pZ pS))
-}
natElimTyFun = natElimPoly @(:~>) @p @n

natElimPoly :: forall (arr :: FunArrow) (p :: (Nat -?> Type) arr) (n :: Nat).
               FunApp arr
            => Sing n
            -> App Nat arr Type p 0
            -> (forall (k :: Nat). Sing k -> App Nat arr Type p k -> App Nat arr Type p (k :+ 1))
            -> App Nat arr Type p n
natElimPoly snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing (sn :: Sing k) -> unsafeCoerce (pS sn (natElimPoly @arr @p @k sn pZ pS))
