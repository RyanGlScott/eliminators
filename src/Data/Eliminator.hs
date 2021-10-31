{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-|
Module:      Data.Eliminator
Copyright:   (C) 2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Dependently typed elimination functions using @singletons@.

This module exports a combination of eliminators whose names are known not to
clash with each other. Potential name conflicts have been resolved by putting
the conflicting names in separate modules:

* "Data.Eliminator" defines 'elimNat', which works over the 'Nat' data type
  from "Data.Nat". For an eliminator that works over 'Nat' from "GHC.TypeNats",
  see "Data.Eliminator.TypeNats".

* "Data.Eliminator" avoids exporting eliminators for @First@ and @Last@ data
  types, as there are multiple data types with these names. If you want
  eliminators for the 'First' and 'Last' data types from "Data.Monoid", import
  them from "Data.Eliminator.Monoid". If you want eliminators for the 'First'
  and 'Last' data types from "Data.Semigroup", import them from
  "Data.Eliminator.Semigroup".

* "Data.Eliminator" avoids exporting eliminators for @Product@ and @Sum@ data
  types, as there are multiple data types with these names. If you want
  eliminators for the 'Product' and 'Sum' data types from "Data.Monoid" or
  "Data.Semigroup", import them from "Data.Eliminator.Monoid" or
  "Data.Eliminator.Semigroup". If you want eliminators for the 'Product' and
  'Sum' data types from "Data.Functor.Product" and "Data.Functor.Sum",
  respectively, import them from "Data.Eliminator.Functor".
-}
module Data.Eliminator (
    -- * Eliminator functions
    -- $eliminators
    elimAll
  , ElimAll
  , elimAny
  , ElimAny
  , elimArg
  , ElimArg
  , elimBool
  , ElimBool
  , elimConst
  , ElimConst
  , elimDown
  , ElimDown
  , elimDual
  , ElimDual
  , elimEither
  , ElimEither
  , elimIdentity
  , ElimIdentity
  , elimList
  , ElimList
  , elimMax
  , ElimMax
  , elimMaybe
  , ElimMaybe
  , elimMin
  , ElimMin
  , elimNat
  , ElimNat
  , elimNonEmpty
  , ElimNonEmpty
  , elimOrdering
  , ElimOrdering
  , elimProxy
  , ElimProxy
  , elimTuple0
  , ElimTuple0
  , elimTuple2
  , ElimTuple2
  , elimTuple3
  , ElimTuple3
  , elimTuple4
  , ElimTuple4
  , elimTuple5
  , ElimTuple5
  , elimTuple6
  , ElimTuple6
  , elimTuple7
  , ElimTuple7
  , elimVoid
  , ElimVoid
  , elimWrappedMonoid
  , ElimWrappedMonoid
  ) where

import Control.Monad.Extra

import Data.Eliminator.Functor
import Data.Eliminator.Monoid
import Data.Eliminator.Semigroup
import Data.Eliminator.TH
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty.Singletons (SNonEmpty(..))
import Data.Nat
import Data.Ord (Down(..))
import Data.Ord.Singletons (SDown(..))
import Data.Proxy.Singletons (SProxy(..))
import Data.Void (Void)

import Language.Haskell.TH (nameBase)
import Language.Haskell.TH.Desugar (tupleNameDegree_maybe)

import Prelude.Singletons

{- $eliminators

These eliminators are defined with propositions of kind @\<Datatype\> ~> 'Type'@
(that is, using the @('~>')@ kind). These eliminators are designed for
defunctionalized (i.e., \"partially applied\") types as predicates,
and as a result, the predicates must be applied manually with 'Apply'.

The naming conventions are:

* If the datatype has an alphanumeric name, its eliminator will have that name
  with @elim@ prepended.

* If the datatype has a symbolic name, its eliminator will have that name
  with @~>@ prepended.
-}

$(concatMapM (\n -> (++) <$> deriveElim n <*> deriveTypeElim n)
             [ ''Bool
             , ''Down
             , ''Either
             , ''Maybe
             , ''Nat
             , ''NonEmpty
             , ''Ordering
             , ''Proxy
             , ''Void
             ])
$(deriveElimNamed     "elimList" ''[])
$(deriveTypeElimNamed "ElimList" ''[])
$(concatMapM (\n -> do deg <- fromMaybeM (fail $ "Internal error: "
                                              ++ nameBase n
                                              ++ " is not the name of a tuple")
                                         (pure $ tupleNameDegree_maybe n)
                       terms <- deriveElimNamed     ("elimTuple" ++ show deg) n
                       types <- deriveTypeElimNamed ("ElimTuple" ++ show deg) n
                       pure $ terms ++ types)
             [''(), ''(,), ''(,,), ''(,,,), ''(,,,,), ''(,,,,,), ''(,,,,,,)])
