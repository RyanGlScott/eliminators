{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module ListSpec where

import Data.Eliminator
import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Type.Equality

import EqualitySpec (cong)

import ListTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

mapPreservesLength :: forall (x :: Type) (y :: Type) (f :: x ~> y) (l :: [x]).
                      SingI l
                   => Length l :~: Length (Map f l)
mapPreservesLength
  = elimList @x @(WhyMapPreservesLengthSym1 f) @l (sing @_ @l) base step
  where
    base :: WhyMapPreservesLength f '[]
    base = Refl

    step :: forall (s :: x) (ss :: [x]).
            Sing s -> Sing ss
         -> WhyMapPreservesLength f ss
         -> WhyMapPreservesLength f (s:ss)
    step _ _ = cong @_ @_ @((:+$$) 1)

mapFusion :: forall (x :: Type) (y :: Type) (z :: Type)
                    (f :: y ~> z) (g :: x ~> y) (l :: [x]).
                    SingI l
                 => Map f (Map g l) :~: Map (f :.$$$ g) l
mapFusion
  = elimList @x @(WhyMapFusionSym2 f g) @l (sing @_ @l) base step
  where
    base :: WhyMapFusion f g '[]
    base = Refl

    step :: forall (s :: x) (ss :: [x]).
            Sing s -> Sing ss
         -> WhyMapFusion f g ss
         -> WhyMapFusion f g (s:ss)
    step _ _ = cong @_ @_ @((:$$) (f @@ (g @@ s)))
