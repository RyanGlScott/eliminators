{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module PolyRecTypes where

import Data.Kind
import Data.Singletons.Base.TH

import Internal

$(singletons [d|
  type WeirdList :: Type -> Type
  data WeirdList a = WeirdNil | WeirdCons a (WeirdList (WeirdList a))
  |])

elimWeirdList :: forall (p :: forall t. WeirdList t ~> Type)
                        a (wl :: WeirdList a).
                 Sing wl
              -> (forall t. p @t @@ WeirdNil)
              -> (forall t (x :: t) (xs :: WeirdList (WeirdList t)).
                         Sing x -> Sing xs -> p @(WeirdList t) @@ xs -> p @t @@ (WeirdCons x xs))
              -> p @a @@ wl
elimWeirdList swl pWeirdNil pWeirdCons = go @a @wl swl
  where
    go :: forall t (wlt :: WeirdList t). Sing wlt -> p @t @@ wlt
    go SWeirdNil = pWeirdNil @t
    go (SWeirdCons (sx :: Sing x) (sxs :: Sing xs)) =
      pWeirdCons @t @x @xs sx sxs (go @(WeirdList t) @xs sxs)

type ElimWeirdList :: forall (p :: forall t. WeirdList t ~> Type)
                   -> forall a.
                      forall (wl :: WeirdList a)
                   -> (forall t. p @t @@ WeirdNil)
                   -> (forall t.
                       forall (x :: t) (xs :: WeirdList (WeirdList t)) ->
                       p @(WeirdList t) @@ xs ~> p @t @@ (WeirdCons x xs))
                   -> p @a @@ wl
type family ElimWeirdList p wl pWeirdNil pWeirdCons where
  forall (p :: forall t. WeirdList t ~> Type)
         (pWeirdNil :: forall t. p @t @@ WeirdNil)
         (pWeirdCons :: forall t. forall (x :: t) (xs :: WeirdList (WeirdList t)) ->
                        p @(WeirdList t) @@ xs ~> p @t @@ (WeirdCons x xs))
         a.
    ElimWeirdList p (WeirdNil @a) pWeirdNil pWeirdCons = pWeirdNil @a
  forall (p :: forall t. WeirdList t ~> Type)
         (pWeirdNil :: forall t. p @t @@ WeirdNil)
         (pWeirdCons :: forall t. forall (x :: t) (xs :: WeirdList (WeirdList t)) ->
                        p @(WeirdList t) @@ xs ~> p @t @@ (WeirdCons x xs))
         a (x :: a) (xs :: WeirdList (WeirdList a)).
    ElimWeirdList p (WeirdCons @a x xs) pWeirdNil pWeirdCons =
      pWeirdCons @a x xs @@ ElimWeirdList p @(WeirdList a) xs pWeirdNil pWeirdCons

elimPropWeirdList :: forall (p :: Prop ~> Prop)
                            (a :: Prop).
                     WeirdList a
                  -> (forall (t :: Prop). p @@ t)
                  -> (forall (t :: Prop).
                             t -> WeirdList (WeirdList t) -> p @@ WeirdList t -> p @@ t)
                  -> p @@ a
elimPropWeirdList wl pWeirdNil pWeirdCons = go @a wl
  where
    go :: forall (t :: Prop). WeirdList t -> p @@ t
    go WeirdNil = pWeirdNil @t
    go (WeirdCons x xs) = pWeirdCons @t x xs (go @(WeirdList t) xs)

type ElimPropWeirdList :: forall (p :: Prop ~> Prop)
                       -> forall (a :: Prop).
                          WeirdList a
                       -> (forall (t :: Prop). p @@ t)
                       -> (forall (t :: Prop).
                                  t ~> WeirdList (WeirdList t) ~> p @@ WeirdList t ~> p @@ t)
                       -> p @@ a
type family ElimPropWeirdList p wl pWeirdNil pWeirdCons where
  forall (p :: Prop ~> Prop)
         (pWeirdNil :: forall (t :: Prop). p @@ t)
         (pWeirdCons :: forall (t :: Prop). t ~> WeirdList (WeirdList t) ~> p @@ WeirdList t ~> p @@ t)
         a.
    ElimPropWeirdList p (WeirdNil @a) pWeirdNil pWeirdCons = pWeirdNil @a
  forall (p :: Prop ~> Prop)
         (pWeirdNil :: forall (t :: Prop). p @@ t)
         (pWeirdCons :: forall (t :: Prop). t ~> WeirdList (WeirdList t) ~> p @@ WeirdList t ~> p @@ t)
         a (x :: a) (xs :: WeirdList (WeirdList a)).
    ElimPropWeirdList p (WeirdCons x xs) pWeirdNil pWeirdCons =
      pWeirdCons @a @@ x @@ xs @@ ElimPropWeirdList p @(WeirdList a) xs pWeirdNil pWeirdCons
