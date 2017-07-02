{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
module PeanoTypes where

import Data.Kind
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

type WhyZipWithVec (a :: Type) (b :: Type) (c :: Type) (n :: Peano)
  = Vec a n -> Vec b n -> Vec c n
$(genDefunSymbols [''WhyZipWithVec])

type WhyTransposeVec (e :: Type) (m :: Peano) (n :: Peano)
  = Vec (Vec e m) n -> Vec (Vec e n) m
$(genDefunSymbols [''WhyTransposeVec])
