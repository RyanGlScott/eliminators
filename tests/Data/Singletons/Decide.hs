{-# LANGUAGE StandaloneKindSignatures #-}
-- TODO RGS: Temporary
module Data.Singletons.Decide where

import Data.Kind
import Data.Void

type Refuted :: Type -> Type
type Refuted a = a -> Void

type Decision :: Type -> Type
data Decision a = Proved a | Disproved (Refuted a)
