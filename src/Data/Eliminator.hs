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
module Data.Eliminator (
    -- * Eliminator functions
    -- ** Eliminators using '(->)'
    -- $eliminators
    elimBool
  , elimEither
  , elimList
  , elimMaybe
  , elimNat
  , elimOrdering
  , elimTuple0

    -- ** Eliminators using '(~>)'
    -- $eliminators-TyFun
  , elimBoolTyFun
  , elimEitherTyFun
  , elimListTyFun
  , elimMaybeTyFun
  , elimNatTyFun
  , elimOrderingTyFun
  , elimTuple0TyFun

    -- ** Arrow-polymorphic eliminators (very experimental)
    -- $eliminators-Poly
  , FunArrow(..)
  , FunType(..)
  , type (-?>)
  , AppType(..)
  , FunApp

  , elimBoolPoly
  , elimEitherPoly
  , elimListPoly
  , elimMaybePoly
  , elimNatPoly
  , elimOrderingPoly
  , elimTuple0Poly
  ) where

import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import Unsafe.Coerce

{- $eliminators

These eliminators are defined with propositions of kind @<Datatype> -> 'Type'@
(that is, using the '(->)' kind). As a result, these eliminators' type signatures
are the most readable in this library, and most closely resemble eliminator functions
in other dependently typed languages.

TODO
-}

elimBool :: forall (p :: Bool -> Type) (b :: Bool).
            Sing b
         -> p False
         -> p True
         -> p b
elimBool = elimBoolPoly @(:->)

elimEither :: forall (a :: Type) (b :: Type) (p :: Either a b -> Type) (e :: Either a b).
              Sing e
           -> (forall (l :: a). Sing l -> p (Left  l))
           -> (forall (r :: b). Sing r -> p (Right r))
           -> p e
elimEither = elimEitherPoly @(:->)

elimList :: forall (a :: Type) (p :: [a] -> Type) (l :: [a]).
            Sing l
         -> p '[]
         -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p xs -> p (x:xs))
         -> p l
elimList = elimListPoly @(:->)

elimMaybe :: forall (a :: Type) (p :: Maybe a -> Type) (m :: Maybe a).
             Sing m
          -> p Nothing
          -> (forall (x :: a). Sing x -> p (Just x))
          -> p m
elimMaybe = elimMaybePoly @(:->)

elimNat :: forall (p :: Nat -> Type) (n :: Nat).
           Sing n
        -> p 0
        -> (forall (k :: Nat). Sing k -> p k -> p (k :+ 1))
        -> p n
elimNat = elimNatPoly @(:->)

elimOrdering :: forall (p :: Ordering -> Type) (o :: Ordering).
                Sing o
             -> p LT
             -> p EQ
             -> p GT
             -> p o
elimOrdering = elimOrderingPoly @(:->)

elimTuple0 :: forall (p :: () -> Type) (u :: ()).
              Sing u
           -> p '()
           -> p u
elimTuple0 = elimTuple0Poly @(:->)

{- $eliminators-TyFun

TODO
-}

elimBoolTyFun :: forall (p :: Bool ~> Type) (b :: Bool).
                 Sing b
              -> p @@ False
              -> p @@ True
              -> p @@ b
elimBoolTyFun = elimBoolPoly @(:~>) @p

elimEitherTyFun :: forall (a :: Type) (b :: Type) (p :: Either a b ~> Type) (e :: Either a b).
                   Sing e
                -> (forall (l :: a). Sing l -> p @@ (Left  l))
                -> (forall (r :: b). Sing r -> p @@ (Right r))
                -> p @@ e
elimEitherTyFun = elimEitherPoly @(:~>) @_ @_ @p

elimListTyFun :: forall (a :: Type) (p :: [a] ~> Type) (l :: [a]).
                 Sing l
              -> p @@ '[]
              -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ xs -> p @@ (x:xs))
              -> p @@ l
elimListTyFun = elimListPoly @(:~>) @_ @p

elimMaybeTyFun :: forall (a :: Type) (p :: Maybe a ~> Type) (m :: Maybe a).
                  Sing m
               -> p @@ Nothing
               -> (forall (x :: a). Sing x -> p @@ (Just x))
               -> p @@ m
elimMaybeTyFun = elimMaybePoly @(:~>) @_ @p

elimNatTyFun :: forall (p :: Nat ~> Type) (n :: Nat).
                Sing n
             -> p @@ 0
             -> (forall (k :: Nat). Sing k -> p @@ k -> p @@ (k :+ 1))
             -> p @@ n
elimNatTyFun = elimNatPoly @(:~>) @p

elimOrderingTyFun :: forall (p :: Ordering ~> Type) (o :: Ordering).
                     Sing o
                  -> p @@ LT
                  -> p @@ EQ
                  -> p @@ GT
                  -> p @@ o
elimOrderingTyFun = elimOrderingPoly @(:~>) @p

elimTuple0TyFun :: forall (p :: () ~> Type) (u :: ()).
                   Sing u
                -> p @@ '()
                -> p @@ u
elimTuple0TyFun = elimTuple0Poly @(:~>) @p

{- $eliminators-Poly

TODO
-}

-- TODO
data FunArrow = (:->) | (:~>)

-- TODO
class FunType (arr :: FunArrow) where
  -- | TODO
  type Fun (k1 :: Type) arr (k2 :: Type) :: Type

-- TODO
class FunType arr => AppType (arr :: FunArrow) where
  -- TODO
  -- Can't be defined in the same class as Fun due to staging restrictions
  type App k1 arr k2 (f :: Fun k1 arr k2) (x :: k1) :: k2

-- TODO
type FunApp arr = (FunType arr, AppType arr)

instance FunType (:->) where
  type Fun k1 (:->) k2 = k1 -> k2

instance AppType (:->) where
  type App k1 (:->) k2 (f :: k1 -> k2) x = f x

instance FunType (:~>) where
  type Fun k1 (:~>) k2 = k1 ~> k2

instance AppType (:~>) where
  type App k1 (:~>) k2 (f :: k1 ~> k2) x = f @@ x

-- TODO
infixr 0 -?>
type (-?>) (k1 :: Type) (k2 :: Type) (arr :: FunArrow) = Fun k1 arr k2

elimBoolPoly :: forall (arr :: FunArrow) (p :: (Bool -?> Type) arr) (b :: Bool).
                FunApp arr
             => Sing b
             -> App Bool arr Type p False
             -> App Bool arr Type p True
             -> App Bool arr Type p b
elimBoolPoly SFalse pF _  = pF
elimBoolPoly STrue  _  pT = pT

elimEitherPoly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (p :: (Either a b -?> Type) arr) (e :: Either a b).
                  FunApp arr
               => Sing e
               -> (forall (l :: a). Sing l -> App (Either a b) arr Type p (Left  l))
               -> (forall (r :: b). Sing r -> App (Either a b) arr Type p (Right r))
               -> App (Either a b) arr Type p e
elimEitherPoly (SLeft  sl) pLeft _  = pLeft  sl
elimEitherPoly (SRight sr) _ pRight = pRight sr

elimListPoly :: forall (arr :: FunArrow) (a :: Type) (p :: ([a] -?> Type) arr) (l :: [a]).
                FunApp arr
             => Sing l
             -> App [a] arr Type p '[]
             -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> App [a] arr Type p xs -> App [a] arr Type p (x:xs))
             -> App [a] arr Type p l
elimListPoly SNil                      pNil _     = pNil
elimListPoly (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (elimListPoly @arr @a @p @xs xs pNil pCons)

elimMaybePoly :: forall (arr :: FunArrow) (a :: Type) (p :: (Maybe a -?> Type) arr) (m :: Maybe a).
                 FunApp arr
              => Sing m
              -> App (Maybe a) arr Type p Nothing
              -> (forall (x :: a). Sing x -> App (Maybe a) arr Type p (Just x))
              -> App (Maybe a) arr Type p m
elimMaybePoly SNothing pNothing _ = pNothing
elimMaybePoly (SJust sx) _ pJust  = pJust sx

elimNatPoly :: forall (arr :: FunArrow) (p :: (Nat -?> Type) arr) (n :: Nat).
               FunApp arr
            => Sing n
            -> App Nat arr Type p 0
            -> (forall (k :: Nat). Sing k -> App Nat arr Type p k -> App Nat arr Type p (k :+ 1))
            -> App Nat arr Type p n
elimNatPoly snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> case toSing (pred nPlusOne) of
                  SomeSing (sn :: Sing k) -> unsafeCoerce (pS sn (elimNatPoly @arr @p @k sn pZ pS))

elimOrderingPoly :: forall (arr :: FunArrow) (p :: (Ordering -?> Type) arr) (o :: Ordering).
                    Sing o
                 -> App Ordering arr Type p LT
                 -> App Ordering arr Type p EQ
                 -> App Ordering arr Type p GT
                 -> App Ordering arr Type p o
elimOrderingPoly SLT pLT _   _   = pLT
elimOrderingPoly SEQ _   pEQ _   = pEQ
elimOrderingPoly SGT _   _   pGT = pGT

elimTuple0Poly :: forall (arr :: FunArrow) (p :: (() -?> Type) arr) (u :: ()).
                  FunApp arr
               => Sing u
               -> App () arr Type p '()
               -> App () arr Type p u
elimTuple0Poly STuple0 pTuple0 = pTuple0
