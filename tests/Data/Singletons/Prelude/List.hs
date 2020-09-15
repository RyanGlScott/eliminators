{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- TODO RGS: Temporary
module Data.Singletons.Prelude.List where

import GHC.TypeNats

type Map :: (a -> b) -> [a] -> [b]
type family Map f l where
  Map _ '[]    = '[]
  Map f (x:xs) = f x : Map f xs

type Length :: [a] -> Nat
type family Length l where
  Length '[]    = 0
  Length (_:xs) = 1 + Length xs
