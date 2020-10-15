{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-|
Module:      Data.Eliminator.TypeNats
Copyright:   (C) 2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

A crude imitation of an eliminator function for 'GHC.TypeNats.Nat'.
-}
module Data.Eliminator.TypeNats (elimNat) where

import Data.Kind (Type)
import Data.Singletons

import GHC.TypeLits.Singletons
import GHC.TypeNats

import Unsafe.Coerce (unsafeCoerce)

-- | Although 'Nat' is not actually an inductive data type in GHC, we can
-- (crudely) pretend that it is using this eliminator.
elimNat :: forall (p :: Nat ~> Type) (n :: Nat).
           Sing n
        -> Apply p 0
        -> (forall (k :: Nat). Sing k -> Apply p k -> Apply p (k + 1))
        -> Apply p n
elimNat snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> withSomeSing (pred nPlusOne) $ \(sn :: Sing k) ->
                  unsafeCoerce (pS sn (elimNat @p @k sn pZ pS))
