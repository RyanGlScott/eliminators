{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Trustworthy #-}
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

import GHC.TypeLits.Singletons ()
import GHC.TypeNats

import Unsafe.Coerce (unsafeCoerce)

-- | Although 'Nat' is not actually an inductive data type in GHC, we can
-- (crudely) pretend that it is using this eliminator.
elimNat :: forall (p :: Nat ~> Type) (n :: Nat).
           Sing n
        -> Apply p 0
        -> (forall (k :: Nat). Sing k -> Apply p k -> Apply p (k + 1))
        -> Apply p n
elimNat snat pZ pS = go @n snat
  where
    go :: forall (n' :: Nat). Sing n' -> Apply p n'
    go snat' =
      case fromSing snat' of
        0        -> unsafeCoerce pZ
        nPlusOne -> withSomeSing (pred nPlusOne) $ \(sk :: Sing k) ->
                      unsafeCoerce (pS sk (go @k sk))
