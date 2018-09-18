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

type WhyMapPreservesLength (f :: x ~> y) (l :: [x])
  = Length l :~: Length (Map f l)
$(genDefunSymbols [''WhyMapPreservesLength])

type WhyMapFusion (f :: y ~> z) (g :: x ~> y) (l :: [x])
  = Map f (Map g l) :~: Map (f .@#@$$$ g) l
$(genDefunSymbols [''WhyMapFusion])
