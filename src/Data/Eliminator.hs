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
  , elimNonEmpty
  , elimOrdering
  , elimTuple0
  , elimTuple2
  , elimTuple3
  , elimTuple4
  , elimTuple5
  , elimTuple6
  , elimTuple7

    -- ** Eliminators using '(~>)'
    -- $eliminators-TyFun
  , elimBoolTyFun
  , elimEitherTyFun
  , elimListTyFun
  , elimMaybeTyFun
  , elimNatTyFun
  , elimNonEmptyTyFun
  , elimOrderingTyFun
  , elimTuple0TyFun
  , elimTuple2TyFun
  , elimTuple3TyFun
  , elimTuple4TyFun
  , elimTuple5TyFun
  , elimTuple6TyFun
  , elimTuple7TyFun

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
  , elimNonEmptyPoly
  , elimNatPoly
  , elimOrderingPoly
  , elimTuple0Poly
  , elimTuple2Poly
  , elimTuple3Poly
  , elimTuple4Poly
  , elimTuple5Poly
  , elimTuple6Poly
  , elimTuple7Poly
  ) where

import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List.NonEmpty (Sing(..))
import Data.Singletons.TypeLits

import Unsafe.Coerce (unsafeCoerce)

{- $eliminators

These eliminators are defined with propositions of kind @\<Datatype\> -> 'Type'@
(that is, using the '(->)' kind). As a result, these eliminators' type signatures
are the most readable in this library, and most closely resemble eliminator functions
in other dependently typed languages.
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

elimNonEmpty :: forall (a :: Type) (p :: NonEmpty a -> Type) (n :: NonEmpty a).
                Sing n
             -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p (x :| xs))
             -> p n
elimNonEmpty = elimNonEmptyPoly @(:->)

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

elimTuple2 :: forall (a :: Type) (b :: Type)
                     (p :: (a, b) -> Type) (t :: (a, b)).
              Sing t
           -> (forall (aa :: a) (bb :: b).
                      Sing aa -> Sing bb
                   -> p '(aa, bb))
           -> p t
elimTuple2 = elimTuple2Poly @(:->)

elimTuple3 :: forall (a :: Type) (b :: Type) (c :: Type)
                     (p :: (a, b, c) -> Type) (t :: (a, b, c)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c).
                      Sing aa -> Sing bb -> Sing cc
                   -> p '(aa, bb, cc))
           -> p t
elimTuple3 = elimTuple3Poly @(:->)

elimTuple4 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type)
                     (p :: (a, b, c, d) -> Type) (t :: (a, b, c, d)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd
                   -> p '(aa, bb, cc, dd))
           -> p t
elimTuple4 = elimTuple4Poly @(:->)

elimTuple5 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type)
                     (p :: (a, b, c, d, e) -> Type) (t :: (a, b, c, d, e)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee
                   -> p '(aa, bb, cc, dd, ee))
           -> p t
elimTuple5 = elimTuple5Poly @(:->)

elimTuple6 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type)
                     (p :: (a, b, c, d, e, f) -> Type) (t :: (a, b, c, d, e, f)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff
                   -> p '(aa, bb, cc, dd, ee, ff))
           -> p t
elimTuple6 = elimTuple6Poly @(:->)

elimTuple7 :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type) (g :: Type)
                     (p :: (a, b, c, d, e, f, g) -> Type) (t :: (a, b, c, d, e, f, g)).
              Sing t
           -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f) (gg :: g).
                      Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff -> Sing gg
                   -> p '(aa, bb, cc, dd, ee, ff, gg))
           -> p t
elimTuple7 = elimTuple7Poly @(:->)

{- $eliminators-TyFun

These eliminators are defined with propositions of kind @\<Datatype\> ~> 'Type'@
(that is, using the '(~>)' kind). These eliminators are designed for
defunctionalized (i.e., \"partially applied\") type families as predicates,
and as a result, the predicates must be applied manually with '(@@)'.
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

elimNonEmptyTyFun :: forall (a :: Type) (p :: NonEmpty a ~> Type) (n :: NonEmpty a).
                     Sing n
                  -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> p @@ (x :| xs))
                  -> p @@ n
elimNonEmptyTyFun = elimNonEmptyPoly @(:~>) @_ @p

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

elimTuple2TyFun :: forall (a :: Type) (b :: Type)
                          (p :: (a, b) ~> Type) (t :: (a, b)).
                   Sing t
                -> (forall (aa :: a) (bb :: b).
                           Sing aa -> Sing bb
                        -> p @@ '(aa, bb))
                -> p @@ t
elimTuple2TyFun = elimTuple2Poly @(:~>) @_ @_ @p

elimTuple3TyFun :: forall (a :: Type) (b :: Type) (c :: Type)
                          (p :: (a, b, c) ~> Type) (t :: (a, b, c)).
                   Sing t
                -> (forall (aa :: a) (bb :: b) (cc :: c).
                           Sing aa -> Sing bb -> Sing cc
                        -> p @@ '(aa, bb, cc))
                -> p @@ t
elimTuple3TyFun = elimTuple3Poly @(:~>) @_ @_ @_ @p

elimTuple4TyFun :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type)
                          (p :: (a, b, c, d) ~> Type) (t :: (a, b, c, d)).
                   Sing t
                -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d).
                           Sing aa -> Sing bb -> Sing cc -> Sing dd
                        -> p @@ '(aa, bb, cc, dd))
                -> p @@ t
elimTuple4TyFun = elimTuple4Poly @(:~>) @_ @_ @_ @_ @p

elimTuple5TyFun :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type)
                          (p :: (a, b, c, d, e) ~> Type) (t :: (a, b, c, d, e)).
                   Sing t
                -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e).
                           Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee
                        -> p @@ '(aa, bb, cc, dd, ee))
                -> p @@ t
elimTuple5TyFun = elimTuple5Poly @(:~>) @_ @_ @_ @_ @_ @p

elimTuple6TyFun :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type)
                          (p :: (a, b, c, d, e, f) ~> Type) (t :: (a, b, c, d, e, f)).
                   Sing t
                -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f).
                           Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff
                        -> p @@ '(aa, bb, cc, dd, ee, ff))
                -> p @@ t
elimTuple6TyFun = elimTuple6Poly @(:~>) @_ @_ @_ @_ @_ @_ @p

elimTuple7TyFun :: forall (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type) (g :: Type)
                          (p :: (a, b, c, d, e, f, g) ~> Type) (t :: (a, b, c, d, e, f, g)).
                   Sing t
                -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f) (gg :: g).
                           Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff -> Sing gg
                        -> p @@ '(aa, bb, cc, dd, ee, ff, gg))
                -> p @@ t
elimTuple7TyFun = elimTuple7Poly @(:~>) @_ @_ @_ @_ @_ @_ @_ @p

{- $eliminators-Poly

Eliminators using '(->)' and eliminators using '(~>)' end up having very similar
implementations - so similar, in fact, that they can be generalized to be polymorphic
over the arrow kind used (as well as the application operator). The 'FunType' and
'AppType' classes capture these notions of abstraction and application, respectively.

Not all eliminators are known to work under this generalized scheme yet (for
instance, eliminators for GADTs).

Chances are, you won't want to use these eliminators directly, since their type
signatures are pretty horrific and don't always play well with type inference.
However, they are provided for the sake of completeness.
-}

-- | An enumeration which represents the possible choices of arrow kind for
-- eliminator functions.
data FunArrow = (:->) -- ^ '(->)'
              | (:~>) -- ^ '(~>)'

-- | Things which have arrow kinds.
class FunType (arr :: FunArrow) where
  -- | An arrow kind.
  type Fun (k1 :: Type) arr (k2 :: Type) :: Type

-- | Things which can be applied.
class FunType arr => AppType (arr :: FunArrow) where
  -- | An application of a 'Fun' to an argument.
  --
  -- Note that this can't be defined in the same class as 'Fun' due to GHC
  -- restrictions on associated type families.
  type App k1 arr k2 (f :: Fun k1 arr k2) (x :: k1) :: k2

-- | Something which has both a 'Fun' and an 'App'.
type FunApp arr = (FunType arr, AppType arr)

instance FunType (:->) where
  type Fun k1 (:->) k2 = k1 -> k2

instance AppType (:->) where
  type App k1 (:->) k2 (f :: k1 -> k2) x = f x

instance FunType (:~>) where
  type Fun k1 (:~>) k2 = k1 ~> k2

instance AppType (:~>) where
  type App k1 (:~>) k2 (f :: k1 ~> k2) x = f @@ x

-- | An infix synonym for 'Fun'.
infixr 0 -?>
type (-?>) (k1 :: Type) (k2 :: Type) (arr :: FunArrow) = Fun k1 arr k2

-- Note: it would be nice to have an infix synonym for 'App' as well, but
-- the order in which the type variable dependencies occur makes this awkward
-- to achieve.

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

elimNonEmptyPoly :: forall (arr :: FunArrow) (a :: Type) (p :: (NonEmpty a -?> Type) arr) (n :: NonEmpty a).
                    FunApp arr
                 => Sing n
                 -> (forall (x :: a) (xs :: [a]). Sing x -> Sing xs -> App (NonEmpty a) arr Type p (x :| xs))
                 -> App (NonEmpty a) arr Type p n
elimNonEmptyPoly (sx :%| sxs) pNECons = pNECons sx sxs

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

elimTuple2Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type)
                         (p :: ((a, b) -?> Type) arr) (t :: (a, b)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b).
                          Sing aa -> Sing bb
                       -> App (a, b) arr Type p '(aa, bb))
               -> App (a, b) arr Type p t
elimTuple2Poly (STuple2 sa sb) pTuple2 = pTuple2 sa sb

elimTuple3Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (c :: Type)
                         (p :: ((a, b, c) -?> Type) arr) (t :: (a, b, c)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b) (cc :: c).
                          Sing aa -> Sing bb -> Sing cc
                       -> App (a, b, c) arr Type p '(aa, bb, cc))
               -> App (a, b, c) arr Type p t
elimTuple3Poly (STuple3 sa sb sc) pTuple3 = pTuple3 sa sb sc

elimTuple4Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (c :: Type) (d :: Type)
                         (p :: ((a, b, c, d) -?> Type) arr) (t :: (a, b, c, d)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d).
                          Sing aa -> Sing bb -> Sing cc -> Sing dd
                       -> App (a, b, c, d) arr Type p '(aa, bb, cc, dd))
               -> App (a, b, c, d) arr Type p t
elimTuple4Poly (STuple4 sa sb sc sd) pTuple4 = pTuple4 sa sb sc sd

elimTuple5Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type)
                         (p :: ((a, b, c, d, e) -?> Type) arr) (t :: (a, b, c, d, e)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e).
                          Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee
                       -> App (a, b, c, d, e) arr Type p '(aa, bb, cc, dd, ee))
               -> App (a, b, c, d, e) arr Type p t
elimTuple5Poly (STuple5 sa sb sc sd se) pTuple5 = pTuple5 sa sb sc sd se

elimTuple6Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type)
                         (p :: ((a, b, c, d, e, f) -?> Type) arr) (t :: (a, b, c, d, e, f)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f).
                          Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff
                       -> App (a, b, c, d, e, f) arr Type p '(aa, bb, cc, dd, ee, ff))
               -> App (a, b, c, d, e, f) arr Type p t
elimTuple6Poly (STuple6 sa sb sc sd se sf) pTuple6 = pTuple6 sa sb sc sd se sf

elimTuple7Poly :: forall (arr :: FunArrow) (a :: Type) (b :: Type) (c :: Type) (d :: Type) (e :: Type) (f :: Type) (g :: Type)
                         (p :: ((a, b, c, d, e, f, g) -?> Type) arr) (t :: (a, b, c, d, e, f, g)).
                  FunApp arr
               => Sing t
               -> (forall (aa :: a) (bb :: b) (cc :: c) (dd :: d) (ee :: e) (ff :: f) (gg :: g).
                          Sing aa -> Sing bb -> Sing cc -> Sing dd -> Sing ee -> Sing ff -> Sing gg
                       -> App (a, b, c, d, e, f, g) arr Type p '(aa, bb, cc, dd, ee, ff, gg))
               -> App (a, b, c, d, e, f, g) arr Type p t
elimTuple7Poly (STuple7 sa sb sc sd se sf sg) pTuple7 = pTuple7 sa sb sc sd se sf sg
