{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-|
Module:      Data.Eliminator
Copyright:   (C) 2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Dependently typed elimination functions using @singletons@.
-}
module Data.Eliminator where

import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import Data.Type.Equality
import Unsafe.Coerce

data FunArrow = (:->) | (:~>)

class FunType (arr :: FunArrow) where
  type Fun (k1 :: Type) arr (k2 :: Type) :: Type

class FunType arr => AppType (arr :: FunArrow) where
  -- Can't be defined in the same class as Fun due to staging restrictions
  type App k1 arr k2 (f :: Fun k1 arr k2) (x :: k1) :: k2

type FunApp arr = (FunType arr, AppType arr)

instance FunType (:->) where
  type Fun k1 (:->) k2 = k1 -> k2

instance AppType (:->) where
  type App k1 (:->) k2 (f :: k1 -> k2) x = f x

instance FunType (:~>) where
  type Fun k1 (:~>) k2 = k1 ~> k2

instance AppType (:~>) where
  type App k1 (:~>) k2 (f :: k1 ~> k2) x = f @@ x

infixr 0 -?>
type (-?>) (k1 :: Type) (k2 :: Type) (arr :: FunArrow) = Fun k1 arr k2

boolElim :: forall (p :: Bool -> Type) (b :: Bool).
            Sing b
         -> p False
         -> p True
         -> p b
boolElim = boolElimPoly @(:->) @p @b

boolElimTyFun :: forall (p :: Bool ~> Type) (b :: Bool).
                 Sing b
              -> p @@ False
              -> p @@ True
              -> p @@ b
boolElimTyFun = boolElimPoly @(:~>) @p @b

boolElimPoly :: forall (arr :: FunArrow) (p :: (Bool -?> Type) arr) (b :: Bool).
                FunApp arr
             => Sing b
             -> App Bool arr Type p False
             -> App Bool arr Type p True
             -> App Bool arr Type p b
boolElimPoly SFalse pF _  = pF
boolElimPoly STrue  _  pT = pT

listElim :: forall (a :: Type) (p :: [a] -> Type) (l :: [a]).
            Sing l
         -> p '[]
         -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p xs -> p (x:xs))
         -> p l
listElim = listElimPoly @(:->) @a @p @l

listElimTyFun :: forall (a :: Type) (p :: [a] ~> Type) (l :: [a]).
                 Sing l
              -> p @@ '[]
              -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ xs -> p @@ (x:xs))
              -> p @@ l
listElimTyFun = listElimPoly @(:~>) @a @p @l

listElimPoly :: forall (arr :: FunArrow) (a :: Type) (p :: ([a] -?> Type) arr) (l :: [a]).
                FunApp arr
             => Sing l
             -> App [a] arr Type p '[]
             -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> App [a] arr Type p xs -> App [a] arr Type p (x:xs))
             -> App [a] arr Type p l
listElimPoly SNil                      pNil _     = pNil
listElimPoly (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (listElimPoly @arr @a @p @xs xs pNil pCons)

natElim :: forall (p :: Nat -> Type) (n :: Nat).
           Sing n
        -> p 0
        -> (forall (k :: Nat). Sing k -> p k -> p (k :+ 1))
        -> p n
natElim = natElimPoly @(:->) @p @n

natElimTyFun :: forall (p :: Nat ~> Type) (n :: Nat).
                Sing n
             -> p @@ 0
             -> (forall (k :: Nat). Sing k -> p @@ k -> p @@ (k :+ 1))
             -> p @@ n
natElimTyFun = natElimPoly @(:~>) @p @n

natElimPoly :: forall (arr :: FunArrow) (p :: (Nat -?> Type) arr) (n :: Nat).
               FunApp arr
            => Sing n
            -> App Nat arr Type p 0
            -> (forall (k :: Nat). Sing k -> App Nat arr Type p k -> App Nat arr Type p (k :+ 1))
            -> App Nat arr Type p n
natElimPoly snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing (sn :: Sing k) -> unsafeCoerce (pS sn (natElimPoly @arr @p @k sn pZ pS))

-----
-- GADT examples
-----

data So :: Bool -> Type where
  Oh :: So True

data instance Sing (z :: So what) where
  SOh :: Sing Oh

soElim :: forall (what :: Bool) (s :: So what) (p :: forall (long_sucker :: Bool). So long_sucker -> Type).
          Sing s
       -> p Oh
       -> p s
soElim SOh pOh = pOh

soElimTyFun :: forall (what :: Bool) (s :: So what) (p :: forall (long_sucker :: Bool). So long_sucker ~> Type).
               Sing s
            -> p @@ Oh
            -> p @@ s
soElimTyFun SOh pOh = pOh

{-
I don't know how to make this kind-check :(

soElimPoly :: forall (arr :: FunArrow) (what :: Bool) (s :: So what)
                     (p :: forall (long_sucker :: Bool). (So long_sucker -?> Type) arr).
              Sing s
           -> App (So True) arr Type p Oh
           -> App (So what) arr Type p s
soElimPoly SOh pOh = pOh
-}

data instance Sing (z :: a :~: b) where
  SRefl :: Sing Refl

(%:~:->) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y -> Type).
            Sing r
         -> p Refl
         -> p r
(%:~:->) SRefl pRefl = pRefl

(%:~:~>) :: forall (k :: Type) (a :: k) (b :: k) (r :: a :~: b) (p :: forall (y :: k). a :~: y ~> Type).
            Sing r
         -> p @@ Refl
         -> p @@ r
(%:~:~>) SRefl pRefl = pRefl

-- (%:~:-?>)

data instance Sing (z :: a :~~: b) where
  SHRefl :: Sing HRefl

(%:~~:->) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y -> Type).
             Sing r
          -> p HRefl
          -> p r
(%:~~:->) SHRefl pHRefl = pHRefl

{-
Why doesn't this typecheck?

(%:~~:~>) :: forall (j :: Type) (k :: Type) (a :: j) (b :: k) (r :: a :~~: b) (p :: forall (z :: Type) (y :: z). a :~~: y ~> Type).
             Sing r
          -> p @@ HRefl
          -> p @@ r
(%:~~:~>) SHRefl pHRefl = pHRefl
-}

-- (%:~~:-?>)

data Obj :: Type where
  MkObj :: o -> Obj

data instance Sing (z :: Obj) where
  SMkObj :: forall (obj :: obiwan). Sing obj -> Sing (MkObj obj)

elimObj :: forall (o :: Obj) (p :: Obj -> Type).
           Sing o
        -> (forall (obj :: Type) (x :: obj). Sing x -> p (MkObj x))
        -> p o
elimObj = elimObjPoly @(:->) @o @p

elimObjTyFun :: forall (o :: Obj) (p :: Obj ~> Type).
                Sing o
             -> (forall (obj :: Type) (x :: obj). Sing x -> p @@ (MkObj x))
             -> p @@ o
elimObjTyFun = elimObjPoly @(:~>) @o @p

elimObjPoly :: forall (arr :: FunArrow) (o :: Obj) (p :: (Obj -?> Type) arr).
               Sing o
            -> (forall (obj :: Type) (x :: obj). Sing x -> App Obj arr Type p (MkObj x))
            -> App Obj arr Type p o
elimObjPoly (SMkObj (x :: Sing (obj :: obiwan))) pMkObj = pMkObj @obiwan @obj x

-----

data WeirdList :: Type -> Type where
  WeirdNil  :: WeirdList a
  WeirdCons :: a -> WeirdList (WeirdList a) -> WeirdList a

data instance Sing (z :: WeirdList a) where
  SWeirdNil  :: Sing WeirdNil
  SWeirdCons :: Sing w -> Sing wws -> Sing (WeirdCons w wws)

elimWeirdList :: forall (a :: Type) (wl :: WeirdList a)
                        (p :: forall (x :: Type). WeirdList x -> Type).
                 Sing wl
              -> (forall (y :: Type). p (WeirdNil :: WeirdList y))
              -> (forall (z :: Type) (x :: z) (xs :: WeirdList (WeirdList z)).
                    Sing x -> Sing xs -> p xs -> p (WeirdCons x xs))
              -> p wl
elimWeirdList SWeirdNil pWeirdNil _ = pWeirdNil
elimWeirdList (SWeirdCons (x :: Sing (x :: z))
                          (xs :: Sing (xs :: WeirdList (WeirdList z))))
              pWeirdNil pWeirdCons
  = pWeirdCons @z @x @xs x xs
      (elimWeirdList @(WeirdList z) @xs @p xs pWeirdNil pWeirdCons)

elimWeirdListTyFun :: forall (a :: Type) (wl :: WeirdList a)
                             (p :: forall (x :: Type). WeirdList x -> Type).
                      Sing wl
                   -> (forall (y :: Type). p (WeirdNil :: WeirdList y))
                   -> (forall (z :: Type) (x :: z) (xs :: WeirdList (WeirdList z)).
                         Sing x -> Sing xs -> p xs -> p (WeirdCons x xs))
                   -> p wl
elimWeirdListTyFun SWeirdNil pWeirdNil _ = pWeirdNil
elimWeirdListTyFun (SWeirdCons (x :: Sing (x :: z))
                          (xs :: Sing (xs :: WeirdList (WeirdList z))))
              pWeirdNil pWeirdCons
  = pWeirdCons @z @x @xs x xs
      (elimWeirdListTyFun @(WeirdList z) @xs @p xs pWeirdNil pWeirdCons)

-- elimWeirdListPoly
