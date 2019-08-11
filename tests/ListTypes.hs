{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module ListTypes where

import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.TH

$(singletons [d|
  type WhyMapPreservesLength :: (x ~> y) -> [x] -> Type
  type WhyMapPreservesLength f l = Length l :~: Length (Map f l)

  type WhyMapFusion :: (y ~> z) -> (x ~> y) -> [x] -> Type
  type WhyMapFusion f g l = Map f (Map g l) :~: Map (f .@#@$$$ g) l
  |])
