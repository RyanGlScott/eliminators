{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
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

boolElim :: forall (p :: Bool -> Type) (b :: Bool).
            Sing b
         -> p False
         -> p True
         -> p b
boolElim SFalse pF _  = pF
boolElim STrue  _  pT = pT

listElim :: forall (a :: Type) (p :: [a] -> Type) (l :: [a]).
            Sing l
         -> p '[]
         -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p xs -> p (x:xs))
         -> p l
listElim SNil         pNil _     = pNil
listElim (SCons x xs) pNil pCons = pCons x xs (listElim xs pNil pCons)

natElim :: forall (p :: Nat -> Type) (n :: Nat).
           Sing n
        -> p 0
        -> (forall k. Sing k -> p k -> p (k :+ 1))
        -> p n
natElim snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing sn -> unsafeCoerce (pS sn (natElim sn pZ pS))
