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
    -- $eliminators
    elimBool
  , elimEither
  , elimList
  , elimMaybe
  , elimNat
  , elimNonEmpty
  , elimOrdering
  , elimTuple0
  , elimTuple2
  , elimTuple3
  , elimTuple4
  , elimTuple5
  , elimTuple6
  , elimTuple7
  ) where

import           Data.Kind (Type)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List.NonEmpty (Sing(..))
import           Data.Singletons.TypeLits

import qualified GHC.TypeLits as TL

import           Unsafe.Coerce (unsafeCoerce)

{- $eliminators

These eliminators are defined with propositions of kind @\<Datatype\> ~> 'Type'@
(that is, using the '(~>)' kind). These eliminators are designed for
defunctionalized (i.e., \"partially applied\") types as predicates,
and as a result, the predicates must be applied manually with '(@@)'.

The naming conventions are:

* If the datatype has an alphanumeric name, its eliminator will have that name
  with @elim-@ prepended.

* If the datatype has a symbolic name, its eliminator will have that name
  with @~>@ prepended.
-}

elimBool :: forall (p :: Bool ~> Type) (b :: Bool).
            Sing b
         -> p @@ False
         -> p @@ True
         -> p @@ b
elimBool SFalse pF _  = pF
elimBool STrue  _  pT = pT

elimEither :: forall (a :: Type) (b :: Type) (p :: Either a b ~> Type) (e :: Either a b).
              Sing e
           -> (forall (l :: a). Sing l -> p @@ (Left  l))
           -> (forall (r :: b). Sing r -> p @@ (Right r))
           -> p @@ e
elimEither (SLeft  sl) pLeft _  = pLeft  sl
elimEither (SRight sr) _ pRight = pRight sr

elimList :: forall (a :: Type) (p :: [a] ~> Type) (l :: [a]).
            Sing l
         -> p @@ '[]
         -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ xs -> p @@ (x:xs))
         -> p @@ l
elimList SNil                      pNil _     = pNil
elimList (SCons x (xs :: Sing xs)) pNil pCons = pCons x xs (elimList @a @p @xs xs pNil pCons)

elimMaybe :: forall (a :: Type) (p :: Maybe a ~> Type) (m :: Maybe a).
             Sing m
          -> p @@ Nothing
          -> (forall (x :: a). Sing x -> p @@ (Just x))
          -> p @@ m
elimMaybe SNothing pNothing _ = pNothing
elimMaybe (SJust sx) _ pJust  = pJust sx

-- | Although 'Nat' is not actually an inductive data type in GHC, we can
-- pretend that it is using this eliminator.
elimNat :: forall (p :: Nat ~> Type) (n :: Nat).
           Sing n
        -> p @@ 0
        -> (forall (k :: Nat). Sing k -> p @@ k -> p @@ (k TL.+ 1))
        -> p @@ n
elimNat snat pZ pS =
  case fromSing snat of
    0        -> unsafeCoerce pZ
    nPlusOne -> withSomeSing (pred nPlusOne) $ \(sn :: Sing k) ->
                  unsafeCoerce (pS sn (elimNat @p @k sn pZ pS))

elimNonEmpty :: forall (a :: Type) (p :: NonEmpty a ~> Type) (n :: NonEmpty a).
                Sing n
             -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ (x :| xs))
             -> p @@ n
elimNonEmpty (sx :%| sxs) pNECons = pNECons sx sxs

elimOrdering :: forall (p :: Ordering ~> Type) (o :: Ordering).
                Sing o
             -> p @@ LT
             -> p @@ EQ
             -> p @@ GT
             -> p @@ o
elimOrdering SLT pLT _   _   = pLT
elimOrdering SEQ _   pEQ _   = pEQ
elimOrdering SGT _   _   pGT = pGT

elimTuple0 :: forall (p :: () ~> Type) (u :: ()).
              Sing u
           -> p @@ '()
           -> p @@ u
elimTuple0 STuple0 pTuple0 = pTuple0

elimTuple2 :: forall (a :: Type) (b :: Type)
                     (p :: (a, b) ~> Type) (t :: (a, b)).
              Sing t
           -> (forall (aa :: a) (bb :: b).
                      Sing aa -> Sing bb
                   -> p @@ '(aa, bb))
           -> p @@ t
elimTuple2 (STuple2 sa sb) pTuple2 = pTuple2 sa sb

elimTuple3 :: forall (a :: Type) (b :: Type) (c :: Type)
                     (p :: (a, b, c) ~> Type) (t :: (a, b, c)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c).
                      Sing aa -> Sing bb -> Sing cc
                   -> p @@ '(aa, bb, cc))
           -> p @@ t
elimTuple3 (STuple3 sa sb sc) pTuple3 = pTuple3 sa sb sc

elimTuple4 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type)
                     (p :: (a, b, c, d) ~> Type) (t :: (a, b, c, d)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd
                   -> p @@ '(aa, bb, cc, dd))
           -> p @@ t
elimTuple4 (STuple4 sa sb sc sd) pTuple4 = pTuple4 sa sb sc sd

elimTuple5 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type)
                     (p :: (a, b, c, d, e) ~> Type) (t :: (a, b, c, d, e)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee
                   -> p @@ '(aa, bb, cc, dd, ee))
           -> p @@ t
elimTuple5 (STuple5 sa sb sc sd se) pTuple5 = pTuple5 sa sb sc sd se

elimTuple6 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type)
                     (p :: (a, b, c, d, e, f) ~> Type) (t :: (a, b, c, d, e, f)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff
                   -> p @@ '(aa, bb, cc, dd, ee, ff))
           -> p @@ t
elimTuple6 (STuple6 sa sb sc sd se sf) pTuple6 = pTuple6 sa sb sc sd se sf

elimTuple7 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type) (g :: Type)
                     (p :: (a, b, c, d, e, f, g) ~> Type) (t :: (a, b, c, d, e, f, g)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f) (gg :: g).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff -> Sing gg
                   -> p @@ '(aa, bb, cc, dd, ee, ff, gg))
           -> p @@ t
elimTuple7 (STuple7 sa sb sc sd se sf sg) pTuple7 = pTuple7 sa sb sc sd se sf sg
