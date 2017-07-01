{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
module PeanoTypes (
    Peano(..)
  , SPeano, Sing(SS, SZ)
  , Vec(..)
  , WhyMapVec

    -- * Defunctionalization symbols
  , ZSym0
  , WhyMapVecSym0, WhyMapVecSym1, WhyMapVecSym2
  ) where

import Data.Kind
import Data.Singletons
import Data.Singletons.TH

data Peano = Z | S Peano
$(genSingletons [''Peano])

data Vec a (n :: Peano) where
  VNil  :: Vec a Z
  VCons :: { vhead :: a, vtail :: Vec a n } -> Vec a (S n)
infixr 5 `VCons`
deriving instance Eq a   => Eq (Vec a n)
deriving instance Ord a  => Ord (Vec a n)
deriving instance Show a => Show (Vec a n)

type WhyMapVec (a :: Type) (b :: Type) (n :: Peano) = Vec a n -> Vec b n
$(genDefunSymbols [''WhyMapVec])
