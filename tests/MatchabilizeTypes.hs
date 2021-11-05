{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module MatchabilizeTypes where

import Data.Singletons

type Matchabilize :: (a ~> b) -> forall (x :: a) -> b
data family Matchabilize

type UnMatchabilize :: k -> k
type family UnMatchabilize a where
  UnMatchabilize (Matchabilize f a) = f @@ a
  UnMatchabilize x                  = x
