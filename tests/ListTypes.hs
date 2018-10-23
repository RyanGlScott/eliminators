{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module ListTypes where

import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.TH

$(singletons [d|
  type WhyMapPreservesLength (f :: x ~> y) (l :: [x])
    = Length l :~: Length (Map f l)

  type WhyMapFusion (f :: y ~> z) (g :: x ~> y) (l :: [x])
    = Map f (Map g l) :~: Map (f .@#@$$$ g) l
  |])
