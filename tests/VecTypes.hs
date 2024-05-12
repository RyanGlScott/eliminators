{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module VecTypes where

import Data.Kind (Type)
import Data.Nat
import Data.Singletons.Base.TH
import Data.Singletons.TH.Options

import Internal

import Prelude.Singletons

$(withOptions defaultOptions{genSingKindInsts = False} $
  singletons [d|
    type Vec :: Type -> Nat -> Type
    data Vec a n where
      VNil :: Vec a Z
      (:#) :: { vhead :: a, vtail :: Vec a n } -> Vec a (S n)
    infixr 5 :#
  |])
deriving instance Eq a   => Eq (Vec a n)
deriving instance Ord a  => Ord (Vec a n)
deriving instance Show a => Show (Vec a n)

instance SingKind a => SingKind (Vec a n) where
  type Demote (Vec a n) = Vec (Demote a) n
  fromSing SVNil      = VNil
  fromSing (x :%# xs) = fromSing x :# fromSing xs
  toSing VNil = SomeSing SVNil
  toSing (x :# xs) =
    withSomeSing x $ \sx ->
      withSomeSing xs $ \sxs ->
        SomeSing $ sx :%# sxs

elimVec :: forall a (p :: forall (k :: Nat). Vec a k ~> Type)
                  (n :: Nat) (v :: Vec a n).
           Sing v
        -> p @@ VNil
        -> (forall (k :: Nat) (x :: a) (xs :: Vec a k).
                   Sing x -> Sing xs -> p @@ xs -> p @@ (x :# xs))
        -> p @@ v
elimVec sv pVNil pVCons = go @n @v sv
  where
    go :: forall (n' :: Nat) (v' :: Vec a n').
          Sing v' -> p @@ v'
    go SVNil = pVNil
    go (sx :%# (sxs :: Sing (xs :: Vec a k))) =
      pVCons sx sxs (go @k @xs sxs)

type ElimVec :: forall a.
                forall (p :: forall (k :: Nat). Vec a k ~> Type)
             -> forall (n :: Nat).
                forall (v :: Vec a n)
             -> p @@ VNil
             -> (forall (k :: Nat).
                 forall (x :: a) (xs :: Vec a k) ->
                 p @@ xs ~> p @@ (x :# xs))
             -> p @@ v
type family ElimVec p v pVNil pVCons where
  forall a (p :: forall (k :: Nat). Vec a k ~> Type)
         (pVNil :: p @@ VNil)
         (pVCons :: forall (k :: Nat).
                    forall (x :: a) (xs :: Vec a k) ->
                    p @@ xs ~> p @@ (x :# xs)).
    ElimVec p VNil pVNil pVCons = pVNil
  forall a (p :: forall (k :: Nat). Vec a k ~> Type)
         (pVNil :: p @@ VNil)
         (pVCons :: forall (k :: Nat).
                    forall (x :: a) (xs :: Vec a k) ->
                    p @@ xs ~> p @@ (x :# xs)) k x xs.
    ElimVec p (x :# (xs :: Vec a k)) pVNil pVCons =
      pVCons x xs @@ ElimVec @a p @k xs pVNil pVCons

elimPropVec :: forall a (p :: Nat ~> Prop) (n :: Nat).
               Vec a n
            -> p @@ Z
            -> (forall (k :: Nat). a -> Vec a k -> p @@ k -> p @@ S k)
            -> p @@ n
elimPropVec v pZ pS = go @n v
  where
    go :: forall (n' :: Nat). Vec a n' -> p @@ n'
    go VNil                   = pZ
    go (x :# (xs :: Vec a k)) = pS x xs (go @k xs)

type ElimPropVec :: forall a.
                    forall (p :: Nat ~> Prop)
                 -> forall (n :: Nat).
                    Vec a n
                 -> p @@ Z
                 -> (forall (k :: Nat). a ~> Vec a k ~> p @@ k ~> p @@ S k)
                 -> p @@ n
type family ElimPropVec p v pZ pS where
  forall a (p :: Nat ~> Prop)
         (pZ :: p @@ Z)
         (pS :: forall (k :: Nat). a ~> Vec a k ~> p @@ k ~> p @@ S k).
    ElimPropVec p VNil pZ pS = pZ
  forall a (p :: Nat ~> Prop)
         (pZ :: p @@ Z)
         (pS :: forall (k :: Nat). a ~> Vec a k ~> p @@ k ~> p @@ S k) k x xs.
    ElimPropVec p (x :# (xs :: Vec a k)) pZ pS =
      pS @@ x @@ xs @@ ElimPropVec @a p @k xs pZ pS

$(singletons [d|
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
  |])
