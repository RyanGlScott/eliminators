{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Module:      Data.Eliminator.Semigroup
Copyright:   (C) 2021 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Eliminator functions for data types in "Data.Semigroup". All of these are
re-exported from "Data.Eliminator" with the following exceptions:

* 'First' and 'Last' are not re-exported from "Data.Eliminator", as they clash
  with eliminators of the same names in "Data.Eliminator.Functor" and
  "Data.Eliminator.Monoid".

* 'Sum' and 'Product' are not re-exported from "Data.Eliminator", as they clash
  with eliminators of the same names in "Data.Eliminator.Functor".
-}
module Data.Eliminator.Semigroup (
    elimAll
  , ElimAll
  , elimAny
  , ElimAny
  , elimArg
  , ElimArg
  , elimDual
  , ElimDual
  , elimFirst
  , ElimFirst
  , elimLast
  , ElimLast
  , elimMax
  , ElimMax
  , elimMin
  , ElimMin
  , elimProduct
  , ElimProduct
  , elimSum
  , ElimSum
  , elimWrappedMonoid
  , ElimWrappedMonoid
  ) where

import Control.Monad.Extra

import Data.Eliminator.Monoid hiding (elimFirst, ElimFirst, elimLast, ElimLast)
import Data.Eliminator.TH
import Data.Semigroup
import Data.Semigroup.Singletons

$(concatMapM (\n -> (++) <$> deriveElim n <*> deriveTypeElim n)
             [ ''Arg
             , ''First
             , ''Last
             , ''Max
             , ''Min
             , ''WrappedMonoid
             ])
