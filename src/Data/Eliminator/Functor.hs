{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Module:      Data.Eliminator.Functor
Copyright:   (C) 2021 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Eliminator functions for data types in the @Data.Functor.*@ module namespace.
All of these are re-exported from "Data.Eliminator" with the exceptions of
'Sum' and 'Product', as these clash with eliminators of the same names in
"Data.Eliminator.Semigroup" and "Data.Eliminator.Monoid".
-}
module Data.Eliminator.Functor (
    elimConst
  , ElimConst
  , elimIdentity
  , ElimIdentity
  , elimProduct
  , ElimProduct
  , elimSum
  , ElimSum
  ) where

import Control.Monad.Extra

import Data.Eliminator.TH
import Data.Functor.Const (Const(..))
import Data.Functor.Const.Singletons (SConst(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Identity.Singletons (SIdentity(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Product.Singletons (SProduct(..))
import Data.Functor.Sum (Sum(..))
import Data.Functor.Sum.Singletons (SSum(..))

$(concatMapM (\n -> (++) <$> deriveElim n <*> deriveTypeElim n)
             [ ''Const
             , ''Identity
             , ''Product
             , ''Sum
             ])
