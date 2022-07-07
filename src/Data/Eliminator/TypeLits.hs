{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Trustworthy #-}
{-|
Module:      Data.Eliminator.TypeLits
Copyright:   (C) 2022 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Crude imitations of eliminator functions for 'GHC.TypeLits.Nat' and
'GHC.TypeLits.Symbol'.
-}
module Data.Eliminator.TypeLits
  ( elimNat
  , elimSymbol
  ) where

import Data.Eliminator.TypeNats
import Data.Kind (Type)
import Data.Singletons
import qualified Data.Text as T

import GHC.TypeLits.Singletons ()
import GHC.TypeLits

import Unsafe.Coerce (unsafeCoerce)

-- | Although 'Nat' is not actually an inductive data type in GHC, we can
-- (crudely) pretend that it is using this eliminator.
elimSymbol :: forall (p :: Symbol ~> Type) (s :: Symbol).
              Sing s
           -> Apply p ""
           -> (forall (c :: Char) (ss :: Symbol).
                 Sing c -> Sing ss -> Apply p ss ->
                 Apply p (ConsSymbol c ss))
           -> Apply p s
elimSymbol ssym pNil pCons = go @s ssym
  where
    go :: forall (s' :: Symbol). Sing s' -> Apply p s'
    go ssym' =
      case T.uncons (fromSing ssym') of
        Nothing      -> unsafeCoerce pNil
        Just (c, ss) -> withSomeSing c  $ \(sc  :: Sing c)  ->
                        withSomeSing ss $ \(sss :: Sing ss) ->
                          unsafeCoerce (pCons sc sss (go @ss sss))
