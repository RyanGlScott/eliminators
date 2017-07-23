{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
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
module Data.Eliminator (
    -- * Eliminator functions
    -- $eliminators
    elimBool
  , elimEither
  , elimList
  , elimMaybe
  , elimNat
  , elimNonEmpty
  , elimOrdering
  , elimTuple0
  , elimTuple2
  , elimTuple3
  , elimTuple4
  , elimTuple5
  , elimTuple6
  , elimTuple7
  ) where

import           Control.Monad.Extra

import           Data.Eliminator.TH
import           Data.Kind (Type)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List.NonEmpty (Sing(..))
import           Data.Singletons.TypeLits

import qualified GHC.TypeLits as TL

import           Language.Haskell.TH.Desugar (tupleNameDegree_maybe)

import           Unsafe.Coerce (unsafeCoerce)

{- $eliminators

These eliminators are defined with propositions of kind @\<Datatype\> ~> 'Type'@
(that is, using the '(~>)' kind). These eliminators are designed for
defunctionalized (i.e., \"partially applied\") types as predicates,
and as a result, the predicates must be applied manually with '(@@)'.

The naming conventions are:

* If the datatype has an alphanumeric name, its eliminator will have that name
  with @elim@ prepended.

* If the datatype has a symbolic name, its eliminator will have that name
  with @~>@ prepended.
-}

$(concatMapM deriveElim [''Bool, ''Either, ''Maybe, ''NonEmpty, ''Ordering])
$(deriveElimNamed "elimList" ''[])
$(concatMapM (\n -> let Just deg = tupleNameDegree_maybe n
                    in deriveElimNamed ("elimTuple" ++ show deg) n)
             [''(), ''(,), ''(,,), ''(,,,), ''(,,,,), ''(,,,,,), ''(,,,,,,)])

-- This is the grimy one we can't define using Template Haskell.

-- | Although 'Nat' is not actually an inductive data type in GHC, we can
-- pretend that it is using this eliminator.
elimNat :: forall (p :: Nat ~> Type) (n :: Nat).
           Sing n
        -> p @@ 0
        -> (forall (k :: Nat). Sing k -> p @@ k -> p @@ (k TL.+ 1))
        -> p @@ n
elimNat snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> withSomeSing (pred nPlusOne) $ \(sn :: Sing k) ->
                  unsafeCoerce (pS sn (elimNat @p @k sn pZ pS))
