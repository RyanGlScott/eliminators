{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
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
    elimAll
  , elimAny
  , elimArg
  , elimBool
  , elimConst
  , elimDown
  , elimDual
  , elimEither
  , elimFirst
  , elimIdentity
  , elimLast
  , elimList
  , elimMax
  , elimMaybe
  , elimMin
  , elimNat
  , elimNonEmpty
  , elimOption
  , elimOrdering
  , elimProduct
  , elimSum
  , elimTuple0
  , elimTuple2
  , elimTuple3
  , elimTuple4
  , elimTuple5
  , elimTuple6
  , elimTuple7
  , elimVoid
  , elimWrappedMonoid
  ) where

import Control.Monad.Extra

import Data.Eliminator.TH
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid hiding (First, Last)
import Data.Nat
import Data.Ord (Down(..))
import Data.Semigroup
import Data.Singletons.Prelude hiding
  (All, Any, Const, Last, Min, Max, Product, Sum)
import Data.Singletons.Prelude.Const (SConst(..))
import Data.Singletons.Prelude.Identity (SIdentity(..))
import Data.Singletons.Prelude.List.NonEmpty (SNonEmpty(..))
import Data.Singletons.Prelude.Monoid hiding (SFirst, SLast)
import Data.Singletons.Prelude.Ord (SDown(..))
import Data.Singletons.Prelude.Semigroup
import Data.Void (Void)

import Language.Haskell.TH.Desugar (tupleNameDegree_maybe)

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

$(concatMapM deriveElim
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
             , ''Option
             , ''Ordering
             , ''Product
             , ''Sum
             , ''Void
             , ''WrappedMonoid
             ])
$(deriveElimNamed "elimList" ''[])
$(concatMapM (\n -> let Just deg = tupleNameDegree_maybe n
                    in deriveElimNamed ("elimTuple" ++ show deg) n)
             [''(), ''(,), ''(,,), ''(,,,), ''(,,,,), ''(,,,,,), ''(,,,,,,)])
