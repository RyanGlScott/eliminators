{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- TODO: Remove this in the next version of singletons
{-# OPTIONS_GHC -Wno-orphans #-}
module DecideTypes where

import Data.Eliminator.TH
import Data.Kind
import Data.Singletons.TH hiding (Decision(..))

import PeanoTypes

-- TODO: Remove these in the next version of singletons
$(genSingletons [''Void])
$(genDefunSymbols [''(~>)])

-- Due to https://github.com/goldfirere/singletons/issues/82, promoting the
-- Decision data type from Data.Singletons.Decide is a tad awkward. To work
-- around these, we define a more general Decision' data type here.
data Decision' p a
  = Proved a
  | Disproved (p @@ a @@ Void)
$(deriveElimNamed "elimDecision" ''Decision')
instance Show a => Show (Decision' p a) where
  showsPrec p (Proved a) =
    showParen (p > 10) $ showString "Proved " . showsPrec 11 a
  showsPrec p (Disproved _) =
    showParen (p > 10) $ showString "Disproved <void>"

type Decision  = Decision' (TyCon2 (->))
type PDecision = Decision' (:~>$)

data instance Sing (z :: Decision' p a) where
  SProved    :: forall (x :: a).         Sing x -> Sing (Proved x)
  SDisproved :: forall (r :: a ~> Void). Sing r -> Sing (Disproved r :: PDecision a)

instance SingKind a => SingKind (PDecision a) where
  type Demote (PDecision a) = Decision (Demote a)
  fromSing (SProved a)    = Proved (fromSing a)
  fromSing (SDisproved r) = Disproved (fromSing r)
  toSing (Proved x)    = withSomeSing x $ SomeSing . SProved
  toSing (Disproved r) = withSomeSing r $ SomeSing . SDisproved

type family PeanoEqConsequences (a :: Peano) (b :: Peano) :: Type where
  PeanoEqConsequences Z      Z      = ()
  PeanoEqConsequences Z      (S _)  = Void
  PeanoEqConsequences (S _)  Z      = Void
  PeanoEqConsequences (S k1) (S k2) = k1 :~: k2
$(genDefunSymbols [''PeanoEqConsequences])

type WhyPeanoEqConsequencesSame (a :: Peano) = PeanoEqConsequences a a
$(genDefunSymbols [''WhyPeanoEqConsequencesSame])

type WhyDecEqZ (k :: Peano) = Decision (Z :~: k)
$(genDefunSymbols [''WhyDecEqZ])

type WhyDecEqS (n :: Peano) (k :: Peano) = Decision (S n :~: k)
$(genDefunSymbols [''WhyDecEqS])

-- The newtype wrapper is needed to work around
-- https://github.com/goldfirere/singletons/issues/198
newtype WhyDecEqPeano (k :: Peano) = WhyDecEqPeano
  { runWhyDecEqPeano :: forall (j :: Peano). Sing j -> Decision (k :~: j) }

type family ListEqConsequences (xxs :: [e]) (yys :: [e]) :: Type where
  ListEqConsequences '[]    '[]    = ()
  ListEqConsequences '[]    (_:_)  = Void
  ListEqConsequences (_:_)  '[]    = Void
  ListEqConsequences (x:xs) (y:ys) = (x :~: y, xs :~: ys)
$(genDefunSymbols [''ListEqConsequences])

type WhyListEqConsequencesSame (es :: [e]) = ListEqConsequences es es
$(genDefunSymbols [''WhyListEqConsequencesSame])

type WhyDecEqNil (es :: [e]) = Decision ('[] :~: es)
$(genDefunSymbols [''WhyDecEqNil])

type WhyDecEqCons (x :: e) (xs :: [e]) (es :: [e]) = Decision ((x:xs) :~: es)
$(genDefunSymbols [''WhyDecEqCons])

type WhyIntermixListEqs1 (x :: e) (xs :: [e]) (ys :: [e]) (k :: e) = (x:xs) :~: (k:ys)
type WhyIntermixListEqs2 (x :: e) (xs :: [e]) (k :: [e])           = (x:xs) :~: (x:k)
$(genDefunSymbols [''WhyIntermixListEqs1, ''WhyIntermixListEqs2])

-- The newtype wrapper is needed to work around
-- https://github.com/goldfirere/singletons/issues/198
newtype WhyDecEqList (l1 :: [e]) = WhyDecEqList
  { runWhyDecEqList :: forall (l2 :: [e]). Sing l2 -> Decision (l1 :~: l2) }
