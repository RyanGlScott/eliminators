{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module PeanoTypes where

import Data.Kind
import Data.Singletons.TH

$(singletons [d|
  data Peano = Z | S Peano

  plus :: Peano -> Peano -> Peano
  plus Z     m = m
  plus (S k) m = S (plus k m)

  times :: Peano -> Peano -> Peano
  times Z     _ = Z
  times (S k) m = plus m (times k m)
  |])

elimPeano :: forall (n :: Peano) (p :: Peano ~> Type).
             Sing n
          -> p @@ Z
          -> (forall (k :: Peano). Sing k -> p @@ k -> p @@ (S k))
          -> p @@ n
elimPeano SZ pZ _ = pZ
elimPeano (SS (sk :: Sing k)) pZ pS = pS sk (elimPeano @k @p sk pZ pS)

data Vec a (n :: Peano) where
  VNil  :: Vec a Z
  VCons :: { vhead :: a, vtail :: Vec a n } -> Vec a (S n)
infixr 5 `VCons`
deriving instance Eq a   => Eq (Vec a n)
deriving instance Ord a  => Ord (Vec a n)
deriving instance Show a => Show (Vec a n)

data instance Sing (z :: Vec a n) where
  SVNil  :: Sing VNil
  SVCons :: { sVhead :: Sing x, sVtail :: Sing xs } -> Sing (VCons x xs)

instance SingKind a => SingKind (Vec a n) where
  type Demote (Vec a n) = Vec (Demote a) n
  fromSing SVNil         = VNil
  fromSing (SVCons x xs) = VCons (fromSing x) (fromSing xs)
  toSing VNil = SomeSing SVNil
  toSing (VCons x xs) =
    withSomeSing x $ \sx ->
      withSomeSing xs $ \sxs ->
        SomeSing $ SVCons sx sxs

instance SingI VNil where
  sing = SVNil

instance (SingI x, SingI xs) => SingI (VCons x xs) where
  sing = SVCons sing sing

elimVec :: forall (a :: Type) (n :: Peano)
                  (p :: forall (k :: Peano). Vec a k ~> Type) (v :: Vec a n).
           Sing v
        -> p @@ VNil
        -> (forall (k :: Peano) (x :: a) (xs :: Vec a k).
                   Sing x -> Sing xs -> p @@ xs -> p @@ (VCons x xs))
        -> p @@ v
elimVec SVNil pVNil _ = pVNil
elimVec (SVCons sx (sxs :: Sing (xs :: Vec a k))) pVNil pVCons =
  pVCons sx sxs (elimVec @a @k @p @xs sxs pVNil pVCons)

type WhyMapVec (a :: Type) (b :: Type) (n :: Peano) = Vec a n -> Vec b n
$(genDefunSymbols [''WhyMapVec])

type WhyZipWithVec (a :: Type) (b :: Type) (c :: Type) (n :: Peano)
  = Vec a n -> Vec b n -> Vec c n
$(genDefunSymbols [''WhyZipWithVec])

type WhyAppendVec (e :: Type) (m :: Peano) (n :: Peano)
  = Vec e n -> Vec e m -> Vec e (Plus n m)
$(genDefunSymbols [''WhyAppendVec])

type WhyTransposeVec (e :: Type) (m :: Peano) (n :: Peano)
  = Vec (Vec e m) n -> Vec (Vec e n) m
$(genDefunSymbols [''WhyTransposeVec])

type WhyConcatVec (e :: Type) (j :: Peano) (n :: Peano) (l :: Vec (Vec e j) n)
  = Vec e (Times n j)
data WhyConcatVecSym (e :: Type) (j :: Peano)
  :: forall (n :: Peano). Vec (Vec e j) n ~> Type
type instance Apply (WhyConcatVecSym e j :: Vec (Vec e j) n ~> Type) l
  = WhyConcatVec e j n l
