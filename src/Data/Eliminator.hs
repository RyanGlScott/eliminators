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
  , elimFirst
  , ElimFirst
  , elimIdentity
  , ElimIdentity
  , elimLast
  , ElimLast
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
  , elimProduct
  , ElimProduct
  , elimProxy
  , ElimProxy
  , elimSum
  , ElimSum
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

import Data.Eliminator.TH
import Data.Functor.Const (Const(..))
import Data.Functor.Const.Singletons (SConst(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Identity.Singletons (SIdentity(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty.Singletons (SNonEmpty(..))
import Data.Monoid hiding (First, Last)
import Data.Monoid.Singletons hiding (SFirst, SLast)
import Data.Nat
import Data.Ord (Down(..))
import Data.Ord.Singletons (SDown(..))
import Data.Proxy.Singletons (SProxy(..))
import Data.Semigroup
import Data.Semigroup.Singletons
import Data.Void (Void)

import Language.Haskell.TH (nameBase)
import Language.Haskell.TH.Desugar (tupleNameDegree_maybe)

import Prelude.Singletons hiding
  (All, Any, Const, Last, Min, Max, Product, Sum)

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
             [ ''All
             , ''Any
             , ''Arg
             , ''Bool
             , ''Const
             , ''Down
             , ''Dual
             , ''Either
             , ''First
             , ''Identity
             , ''Last
             , ''Max
             , ''Maybe
             , ''Min
             , ''Nat
             , ''NonEmpty
             , ''Ordering
             , ''Product
             , ''Proxy
             , ''Sum
             , ''Void
             , ''WrappedMonoid
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
