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
Module:      Data.Eliminator.Monoid
Copyright:   (C) 2021 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Eliminator functions for 'First' and 'Last' from "Data.Monoid". These are
defined in their own module to avoid clashing with eliminators of the same
names in "Data.Eliminator", which work over the 'First' and 'Last' newtypes
from "Data.Semigroup" instead.
-}
module Data.Eliminator.Monoid (
    elimFirst
  , ElimFirst
  , elimLast
  , ElimLast
  ) where

import Control.Monad.Extra

import Data.Eliminator.TH
import Data.Monoid (First(..), Last(..))
import Data.Monoid.Singletons (SFirst(..), SLast(..))

$(concatMapM (\n -> (++) <$> deriveElim n <*> deriveTypeElim n)
             [''First, ''Last])
