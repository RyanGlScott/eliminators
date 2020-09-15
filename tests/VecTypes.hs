{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnsaturatedTypeFamilies #-}
module VecTypes where

import Data.Kind (Type)
import Data.Nat
import Data.Singletons
import Data.Singletons.Prelude.Num
import Internal

type Vec :: Type -> Nat -> Type
data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Z
  (:#) :: { vhead :: a, vtail :: Vec a n } -> Vec a (S n)
infixr 5 :#
deriving instance Eq a   => Eq (Vec a n)
deriving instance Ord a  => Ord (Vec a n)
deriving instance Show a => Show (Vec a n)

type SVec :: Vec a n -> Type
data SVec v where
  SVNil :: SVec VNil
  (:%#) :: { sVhead :: Sing x, sVtail :: Sing xs } -> SVec (x :# xs)
type instance Sing = SVec
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

elimVec :: forall {m} a (p :: forall (k :: Nat). Vec a k -> @m Type)
                  (n :: Nat) (v :: Vec a n).
           Sing v
        -> p VNil
        -> (forall (k :: Nat) (x :: a) (xs :: Vec a k).
                   Sing x -> Sing xs -> p xs -> p (x :# xs))
        -> p v
elimVec SVNil pVNil _ = pVNil
elimVec (sx :%# (sxs :: Sing (xs :: Vec a k))) pVNil pVCons =
  pVCons sx sxs (elimVec @a @p @k @xs sxs pVNil pVCons)

type ElimVec :: forall a.
                forall (p :: forall (k :: Nat). Vec a k -> Type)
             -> forall (n :: Nat).
                forall (v :: Vec a n)
             -> p VNil
             -> (forall (k :: Nat).
                 forall (x :: a) (xs :: Vec a k) ->
                 p xs -> p (x :# xs))
             -> p v
type family ElimVec p v pVNil pVCons where
  forall a (p :: forall (k :: Nat). Vec a k -> Type)
         (pVNil :: p VNil)
         (pVCons :: forall (k :: Nat).
                    forall (x :: a) (xs :: Vec a k) ->
                    p xs -> p (x :# xs)).
    ElimVec p VNil pVNil pVCons = pVNil
  forall a (p :: forall (k :: Nat). Vec a k -> Type)
         (pVNil :: p VNil)
         (pVCons :: forall (k :: Nat).
                    forall (x :: a) (xs :: Vec a k) ->
                    p xs -> p (x :# xs)) k x xs.
    ElimVec p (x :# (xs :: Vec a k)) pVNil pVCons =
      pVCons x xs (ElimVec @a p @k xs pVNil pVCons)

elimPropVec :: forall {m} a (p :: Nat -> @m Prop) (n :: Nat).
               Vec a n
            -> p Z
            -> (forall (k :: Nat). a -> Vec a k -> p k -> p (S k))
            -> p n
elimPropVec VNil pZ _ = pZ
elimPropVec (x :# (xs :: Vec a k)) pZ pS =
  pS x xs (elimPropVec @a @p @k xs pZ pS)

type ElimPropVec :: forall a.
                    forall (p :: Nat -> Prop)
                 -> forall (n :: Nat).
                    Vec a n
                 -> p Z
                 -> (forall (k :: Nat). a -> Vec a k -> p k -> p (S k))
                 -> p n
type family ElimPropVec p v pZ pS where
  forall a (p :: Nat -> Prop)
         (pZ :: p Z)
         (pS :: forall (k :: Nat). a -> Vec a k -> p k -> p (S k)).
    ElimPropVec p VNil pZ pS = pZ
  forall a (p :: Nat -> Prop)
         (pZ :: p Z)
         (pS :: forall (k :: Nat). a -> Vec a k -> p k -> p (S k)) k x xs.
    ElimPropVec p (x :# (xs :: Vec a k)) pZ pS =
      pS x xs (ElimPropVec @a p @k xs pZ pS)

type WhyMapVec :: Type -> Type -> Nat -> Type
type WhyMapVec a b n = Vec a n -> Vec b n

type WhyZipWithVec :: Type -> Type -> Type -> Nat -> Type
type WhyZipWithVec a b c n = Vec a n -> Vec b n -> Vec c n

type WhyAppendVec :: Type -> Nat -> Nat -> Type
type WhyAppendVec e m n = Vec e n -> Vec e m -> Vec e (n + m)

type WhyTransposeVec :: Type -> Nat -> Nat -> Type
type WhyTransposeVec e m n = Vec (Vec e m) n -> Vec (Vec e n) m

type WhyConcatVec :: Vec (Vec e j) n -> Type
type WhyConcatVec (l :: Vec (Vec e j) n) = Vec e (n * j)
