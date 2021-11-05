{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Module:      Data.Eliminator.Monoid
Copyright:   (C) 2021 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Eliminator functions for data types in "Data.Monoid". All of these are
re-exported from "Data.Eliminator" with the following exceptions:

* 'First' and 'Last' are not re-exported from "Data.Eliminator", as they clash
  with eliminators of the same names in "Data.Eliminator.Functor" and
  "Data.Eliminator.Semigroup".

* 'Sum' and 'Product' are not re-exported from "Data.Eliminator", as they clash
  with eliminators of the same names in "Data.Eliminator.Functor".
-}
module Data.Eliminator.Monoid (
    elimAll
  , ElimAll
  , elimAny
  , ElimAny
  , elimDual
  , ElimDual
  , elimFirst
  , ElimFirst
  , elimLast
  , ElimLast
  , elimProduct
  , ElimProduct
  , elimSum
  , ElimSum
  ) where

import Control.Monad.Extra

import Data.Eliminator.TH
import Data.Monoid
import Data.Monoid.Singletons

$(concatMapM (\n -> (++) <$> deriveElim n <*> deriveTypeElim n)
             [ ''All
             , ''Any
             , ''Dual
             , ''First
             , ''Last
             , ''Product
             , ''Sum
             ])
