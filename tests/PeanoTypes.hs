{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module PeanoTypes where

import Data.Eliminator.TH
import Data.Kind
import Data.Singletons.TH

$(singletons [d|
  data Peano = Z | S Peano

  infixl 6 `plus`
  plus :: Peano -> Peano -> Peano
  plus Z     m = m
  plus (S k) m = S (plus k m)

  infixl 7 `times`
  times :: Peano -> Peano -> Peano
  times Z     _ = Z
  times (S k) m = plus m (times k m)
  |])
$(deriveElim ''Peano)

data Vec a (n :: Peano) where
  VNil :: Vec a Z
  (:#) :: { vhead :: a, vtail :: Vec a n } -> Vec a (S n)
infixr 5 :#
deriving instance Eq a   => Eq (Vec a n)
deriving instance Ord a  => Ord (Vec a n)
deriving instance Show a => Show (Vec a n)

data instance Sing (z :: Vec a n) where
  SVNil :: Sing VNil
  (:%#) :: { sVhead :: Sing x, sVtail :: Sing xs } -> Sing (x :# xs)
type SVec = (Sing :: Vec a n -> Type)
infixr 5 :%#

instance SingKind a => SingKind (Vec a n) where
  type Demote (Vec a n) = Vec (Demote a) n
  fromSing SVNil      = VNil
  fromSing (x :%# xs) = fromSing x :# fromSing xs
  toSing VNil = SomeSing SVNil
  toSing (x :# xs) =
    withSomeSing x $ \sx ->
      withSomeSing xs $ \sxs ->
        SomeSing $ sx :%# sxs

instance SingI VNil where
  sing = SVNil

instance (SingI x, SingI xs) => SingI (x :# xs) where
  sing = sing :%# sing

elimVec :: forall (a :: Type) (n :: Peano)
                  (p :: forall (k :: Peano). Vec a k ~> Type) (v :: Vec a n).
           Sing v
        -> p @@ VNil
        -> (forall (k :: Peano) (x :: a) (xs :: Vec a k).
                   Sing x -> Sing xs -> p @@ xs -> p @@ (x :# xs))
        -> p @@ v
elimVec SVNil pVNil _ = pVNil
elimVec (sx :%# (sxs :: Sing (xs :: Vec a k))) pVNil pVCons =
  pVCons sx sxs (elimVec @a @k @p @xs sxs pVNil pVCons)

type WhyMapVec (a :: Type) (b :: Type) (n :: Peano) = Vec a n -> Vec b n
$(genDefunSymbols [''WhyMapVec])

type WhyZipWithVec (a :: Type) (b :: Type) (c :: Type) (n :: Peano)
  = Vec a n -> Vec b n -> Vec c n
$(genDefunSymbols [''WhyZipWithVec])

type WhyAppendVec (e :: Type) (m :: Peano) (n :: Peano)
  = Vec e n -> Vec e m -> Vec e (n `Plus` m)
$(genDefunSymbols [''WhyAppendVec])

type WhyTransposeVec (e :: Type) (m :: Peano) (n :: Peano)
  = Vec (Vec e m) n -> Vec (Vec e n) m
$(genDefunSymbols [''WhyTransposeVec])

type WhyConcatVec (e :: Type) (j :: Peano) (n :: Peano) (l :: Vec (Vec e j) n)
  = Vec e (n `Times` j)
data WhyConcatVecSym (e :: Type) (j :: Peano)
  :: forall (n :: Peano). Vec (Vec e j) n ~> Type
type instance Apply (WhyConcatVecSym e j :: Vec (Vec e j) n ~> Type) l
  = WhyConcatVec e j n l
