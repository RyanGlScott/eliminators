{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module ListTypes where

import Data.Kind
import Data.List.Singletons
import Data.Singletons.TH
import Prelude.Singletons

$(singletons [d|
  type WhyMapPreservesLength :: (x ~> y) -> [x] -> Type
  type WhyMapPreservesLength f l = Length l :~: Length (Map f l)

  type WhyMapFusion :: (y ~> z) -> (x ~> y) -> [x] -> Type
  type WhyMapFusion f g l = Map f (Map g l) :~: Map (f .@#@$$$ g) l
  |])
