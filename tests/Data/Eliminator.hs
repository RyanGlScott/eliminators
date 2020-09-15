{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnsaturatedTypeFamilies #-}
-- TODO RGS: Temporary
module Data.Eliminator where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude

elimList :: forall {m} a (p :: [a] -> @m Type) (l :: [a]).
            Sing l
         -> p '[]
         -> (forall (x :: a). Sing x -> forall (xs :: [a]). Sing xs -> p xs -> p (x:xs))
         -> p l
elimList SNil           pNil _pCons = pNil
elimList (SCons sx sxs) pNil  pCons = pCons sx sxs (elimList @a @p sxs pNil pCons)

type ElimList :: forall a.
                 forall (p :: [a] -> Type) (l :: [a])
              -> p '[]
              -> (forall (x :: a) (xs :: [a]) -> p xs -> p (x:xs))
              -> p l
type family ElimList p l pNil pCons where
  forall a (p :: [a] -> Type)
         (pNil :: p '[]) (pCons :: forall (x :: a) (xs :: [a]) -> p xs -> p (x:xs)).
    ElimList p '[] pNil pCons = pNil
  forall a (p :: [a] -> Type)
         (pNil :: p '[]) (pCons :: forall (x :: a) (xs :: [a]) -> p xs -> p (x:xs))
         (x :: a) (xs :: [a]).
    ElimList p (x:xs) pNil pCons = pCons x xs (ElimList p xs pNil pCons)

elimNat :: forall {m} (p :: Nat -> @m Type) (s :: Nat).
           Sing s
        -> p Z
        -> (forall (n :: Nat). Sing n -> p n -> p (S n))
        -> p s
elimNat SZ      pZ _pS = pZ
elimNat (SS sn) pZ  pS = pS sn (elimNat @p sn pZ pS)

type ElimNat :: forall (p :: Nat -> Type) (s :: Nat)
             -> p Z
             -> (forall (n :: Nat) -> p n -> p (S n))
             -> p s
type family ElimNat p s pZ pS where
  forall (p :: Nat -> Type)
         (pZ :: p Z) (pS :: forall (n :: Nat) -> p n -> p (S n)).
    ElimNat p Z pZ pS = pZ
  forall (p :: Nat -> Type)
         (pZ :: p Z) (pS :: forall (n :: Nat) -> p n -> p (S n))
         (n :: Nat).
    ElimNat p (S n) pZ pS = pS n (ElimNat p n pZ pS)
