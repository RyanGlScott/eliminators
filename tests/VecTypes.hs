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
module VecTypes where

import Data.Eliminator.TH
import Data.Kind
import Data.Nat
import Data.Singletons.Prelude.Num
import Data.Singletons.TH

$(deriveElim ''Nat)

data Vec :: Type -> Nat -> Type where
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

elimVec :: forall (a :: Type) (n :: Nat)
                  (p :: forall (k :: Nat). Vec a k ~> Type) (v :: Vec a n).
           Sing v
        -> p @@ VNil
        -> (forall (k :: Nat) (x :: a) (xs :: Vec a k).
                   Sing x -> Sing xs -> p @@ xs -> p @@ (x :# xs))
        -> p @@ v
elimVec SVNil pVNil _ = pVNil
elimVec (sx :%# (sxs :: Sing (xs :: Vec a k))) pVNil pVCons =
  pVCons sx sxs (elimVec @a @k @p @xs sxs pVNil pVCons)

type WhyMapVec (a :: Type) (b :: Type) (n :: Nat) = Vec a n -> Vec b n
$(genDefunSymbols [''WhyMapVec])

type WhyZipWithVec (a :: Type) (b :: Type) (c :: Type) (n :: Nat)
  = Vec a n -> Vec b n -> Vec c n
$(genDefunSymbols [''WhyZipWithVec])

type WhyAppendVec (e :: Type) (m :: Nat) (n :: Nat)
  = Vec e n -> Vec e m -> Vec e (n :+ m)
$(genDefunSymbols [''WhyAppendVec])

type WhyTransposeVec (e :: Type) (m :: Nat) (n :: Nat)
  = Vec (Vec e m) n -> Vec (Vec e n) m
$(genDefunSymbols [''WhyTransposeVec])

type WhyConcatVec (e :: Type) (j :: Nat) (n :: Nat) (l :: Vec (Vec e j) n)
  = Vec e (n :* j)
data WhyConcatVecSym (e :: Type) (j :: Nat)
  :: forall (n :: Nat). Vec (Vec e j) n ~> Type
type instance Apply (WhyConcatVecSym e j :: Vec (Vec e j) n ~> Type) l
  = WhyConcatVec e j n l