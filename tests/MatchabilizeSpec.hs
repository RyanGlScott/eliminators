{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module MatchabilizeSpec where

import Data.Eliminator
import Data.Type.Equality

import MatchabilizeTypes

import Prelude.Singletons

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

type ElimMaybeSimple :: b -> (a ~> b) -> Maybe a -> b
type ElimMaybeSimple (n :: b) j m =
    UnMatchabilize (ElimMaybe (ConstSym1 b) m n (Matchabilize j))

test1 :: ElimMaybeSimple "a" IdSym0 Nothing :~: "a"
test1 = Refl

test2 :: ElimMaybeSimple "a" IdSym0 (Just "b") :~: "b"
test2 = Refl
