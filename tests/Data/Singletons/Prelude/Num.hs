{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- TODO RGS: Temporary
module Data.Singletons.Prelude.Num where

class PNum a where
  infixl 6 +, *
  type (x :: a) + (y :: a) :: a
  type (x :: a) * (y :: a) :: a
