{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
module ListSpec where

import Data.Eliminator
import Data.List.Singletons
import Data.Type.Equality

import EqualitySpec (cong)
import ListTypes

import Prelude.Singletons

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

mapPreservesLength :: forall x y (f :: x ~> y) (l :: [x]).
                      SingI l
                   => Length l :~: Length (Map f l)
mapPreservesLength
  = elimList @x @(WhyMapPreservesLengthSym1 f) @l (sing @l) base step
  where
    base :: WhyMapPreservesLength f '[]
    base = Refl

    step :: forall (s :: x). Sing s
         -> forall (ss :: [x]). Sing ss
         -> WhyMapPreservesLength f ss
         -> WhyMapPreservesLength f (s:ss)
    step _ _ = cong @_ @_ @((+@#@$$) 1)

mapFusion :: forall x y z
                    (f :: y ~> z) (g :: x ~> y) (l :: [x]).
                    SingI l
                 => Map f (Map g l) :~: Map (f .@#@$$$ g) l
mapFusion
  = elimList @x @(WhyMapFusionSym2 f g) @l (sing @l) base step
  where
    base :: WhyMapFusion f g '[]
    base = Refl

    step :: forall (s :: x). Sing s
         -> forall (ss :: [x]). Sing ss
         -> WhyMapFusion f g ss
         -> WhyMapFusion f g (s:ss)
    step _ _ = cong @_ @_ @((:@#@$$) (f @@ (g @@ s)))
