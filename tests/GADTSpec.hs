{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module GADTSpec where

import Data.Kind
import Data.Singletons

import Internal

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = pure ()

-----

type So :: Bool -> Type
data So b where
  Oh :: So True

type SSo :: So what -> Type
data SSo s where
  SOh :: SSo Oh
type instance Sing = SSo

elimSo :: forall (p :: forall (long_sucker :: Bool). So long_sucker ~> Type)
                 (what :: Bool) (s :: So what).
          Sing s
       -> p @@ Oh
       -> p @@ s
elimSo SOh pOh = pOh

type ElimSo :: forall (p :: forall (long_sucker :: Bool). So long_sucker ~> Type)
            -> forall (what :: Bool).
               forall (s :: So what)
            -> p @@ Oh
            -> p @@ s
type family ElimSo p s pOh where
  forall (p :: forall (long_sucker :: Bool). So long_sucker ~> Type)
         (pOh :: p @@ Oh).
    ElimSo p Oh pOh = pOh

elimPropSo :: forall (p :: Bool ~> Prop) (what :: Bool).
              So what
           -> p @@ True
           -> p @@ what
elimPropSo Oh pOh = pOh

type ElimPropSo :: forall (p :: Bool ~> Prop)
                -> forall (what :: Bool).
                   So what
                -> p @@ True
                -> p @@ what
type family ElimPropSo p s pOh where
  forall (p :: Bool ~> Prop) (pOh :: p @@ True).
    ElimPropSo p Oh pOh = pOh

type Flarble :: Type -> Type -> Type
data Flarble a b where
  MkFlarble1 :: a -> Flarble a b
  MkFlarble2 :: a ~ Bool => Flarble a (Maybe b)

type SFlarble :: Flarble a b -> Type
data SFlarble f where
  SMkFlarble1 :: Sing x -> SFlarble (MkFlarble1 x)
  SMkFlarble2 :: SFlarble MkFlarble2
type instance Sing = SFlarble

elimFlarble :: forall (p :: forall x y. Flarble x y ~> Type)
                      a b (f :: Flarble a b).
               Sing f
            -> (forall a' b' (x :: a'). Sing x -> p @@ (MkFlarble1 x :: Flarble a' b'))
            -> (forall b'. p @@ (MkFlarble2 :: Flarble Bool (Maybe b')))
            -> p @@ f
elimFlarble s@(SMkFlarble1 sx) pMkFlarble1 _ =
  case s of
    (_ :: Sing (MkFlarble1 x :: Flarble a' b')) -> pMkFlarble1 @a' @b' @x sx
elimFlarble s@SMkFlarble2 _ pMkFlarble2 =
  case s of
    (_ :: Sing (MkFlarble2 :: Flarble Bool (Maybe b'))) -> pMkFlarble2 @b'

type ElimFlarble ::
     forall (p :: forall x y. Flarble x y ~> Type)
  -> forall a b.
     forall (f :: Flarble a b)
  -> (forall a' b'. forall (x :: a') -> p @@ (MkFlarble1 x :: Flarble a' b'))
  -> (forall b'. p @@ (MkFlarble2 :: Flarble Bool (Maybe b')))
  -> p @@ f
type family ElimFlarble p f pMkFlarble1 pMkFlarble2 where
  forall (p :: forall x y. Flarble x y ~> Type) a b
         (pMkFlarble1 :: forall a' b'. forall (x :: a') -> p @@ (MkFlarble1 x :: Flarble a' b'))
         (pMkFlarble2 :: forall b'. p @@ (MkFlarble2 :: Flarble Bool (Maybe b'))) x.
    ElimFlarble p (MkFlarble1 x :: Flarble a b) pMkFlarble1 pMkFlarble2 =
      pMkFlarble1 @a @b x
  forall (p :: forall x y. Flarble x y ~> Type)
         (pMkFlarble1 :: forall a' b'. forall (x :: a') -> p @@ (MkFlarble1 x :: Flarble a' b'))
         (pMkFlarble2 :: forall b'. p @@ (MkFlarble2 :: Flarble Bool (Maybe b'))) b'.
    ElimFlarble p (MkFlarble2 :: Flarble Bool (Maybe b')) pMkFlarble1 pMkFlarble2 =
      pMkFlarble2 @b'

elimPropFlarble :: forall (p :: Type ~> Type ~> Prop) a b.
                   Flarble a b
                -> (forall a' b'. a' -> p @@ a' @@ b')
                -> (forall b'. p @@ Bool @@ Maybe b')
                -> p @@ a @@ b
elimPropFlarble f@(MkFlarble1 x) pMkFlarble1 _ =
  case f of
    (_ :: Flarble a' b') -> pMkFlarble1 @a' @b' x
elimPropFlarble f@MkFlarble2 _ pMkFlarble2 =
  case f of
    (_ :: Flarble Bool (Maybe b')) -> pMkFlarble2 @b'

type ElimPropFlarble ::
     forall (p :: Type ~> Type ~> Prop)
  -> forall a b.
     Flarble a b
  -> (forall a' b'. a' ~> p @@ a' @@ b')
  -> (forall b'. p @@ Bool @@ Maybe b')
  -> p @@ a @@ b
type family ElimPropFlarble p f pMkFlarble1 pMkFlarble2 where
  forall (p :: Type ~> Type ~> Prop) a b
         (pMkFlarble1 :: forall a' b'. a' ~> p @@ a' @@ b')
         (pMkFlarble2 :: forall b'. p @@ Bool @@ Maybe b') x.
    ElimPropFlarble p (MkFlarble1 x :: Flarble a b) pMkFlarble1 pMkFlarble2 =
      pMkFlarble1 @a @b @@ x
  forall (p :: Type ~> Type ~> Prop)
         (pMkFlarble1 :: forall a' b'. a' ~> p @@ a' @@ b')
         (pMkFlarble2 :: forall b'. p @@ Bool @@ Maybe b') b'.
    ElimPropFlarble p (MkFlarble2 :: Flarble Bool (Maybe b')) pMkFlarble1 pMkFlarble2 =
      pMkFlarble2 @b'

type Obj :: Type
data Obj where
  MkObj :: o -> Obj

type SObj :: Obj -> Type
data SObj o where
  SMkObj :: forall obiwan (obj :: obiwan). Sing obj -> SObj (MkObj obj)
type instance Sing = SObj

elimObj :: forall (p :: Obj ~> Type) (o :: Obj).
           Sing o
        -> (forall obj (x :: obj). Sing x -> p @@ MkObj x)
        -> p @@ o
elimObj (SMkObj (sx :: Sing (x :: obj))) pMkObj = pMkObj @obj @x sx

type ElimObj :: forall (p :: Obj ~> Type)
                       (o :: Obj)
             -> (forall obj. forall (x :: obj) -> p @@ MkObj x)
             -> p @@ o
type family ElimObj p o pMkObj where
  forall (p :: Obj ~> Type)
         (pMkObj :: forall obj. forall (x :: obj) -> p @@ MkObj x)
         obj (x :: obj).
    ElimObj p (MkObj (x :: obj)) pMkObj = pMkObj @obj x

elimPropObj :: forall (p :: Prop).
               Obj
            -> (forall obj. obj -> p)
            -> p
elimPropObj (MkObj o) pMkObj = pMkObj o

type ElimPropObj :: forall (p :: Prop) -> Obj -> (forall obj. obj ~> p) -> p
type family ElimPropObj p o pMkObj where
  forall (p :: Prop) (pMkObj :: forall obj. obj ~> p) o.
    ElimPropObj p (MkObj o) pMkObj = pMkObj @@ o
