{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module DecideTypes where

import Data.Kind
import Data.Nat
import Data.Singletons.TH hiding (Decision(..))

-- Due to https://github.com/goldfirere/singletons/issues/82, promoting the
-- Decision data type from Data.Singletons.Decide is a tad awkward. To work
-- around these, we define a more general Decision' data type here.
data Decision' p a
  = Proved a
  | Disproved (p @@ a @@ Void)

elimDecision :: forall (a :: Type) (p :: PDecision a ~> Type) (d :: PDecision a).
                Sing d
             -> (forall (yes :: a). Sing yes -> p @@ (Proved yes))
             -> (forall (no :: a ~> Void). Sing no -> p @@ (Disproved no))
             -> p @@ d
elimDecision (SProved yes)   pProved _          = pProved yes
elimDecision (SDisproved no) _       pDisproved = pDisproved no

instance Show a => Show (Decision' p a) where
  showsPrec p (Proved a) =
    showParen (p > 10) $ showString "Proved " . showsPrec 11 a
  showsPrec p (Disproved _) =
    showParen (p > 10) $ showString "Disproved <void>"

type Decision  = Decision' (TyCon (->))
type PDecision = Decision' (~>@#@$)

data instance Sing (z :: PDecision a) where
  -- It would be lovely to not have to write those (:: PDecision a) kind
  -- ascriptions in the return types of each constructor.
  -- See https://ghc.haskell.org/trac/ghc/ticket/14111.
  SProved    :: forall a (x :: a).         Sing x -> Sing (Proved x    :: PDecision a)
  SDisproved :: forall a (r :: a ~> Void). Sing r -> Sing (Disproved r :: PDecision a)

instance SingKind a => SingKind (PDecision a) where
  type Demote (PDecision a) = Decision (Demote a)
  fromSing (SProved a)    = Proved (fromSing a)
  fromSing (SDisproved r) = Disproved (fromSing r)
  toSing (Proved x)    = withSomeSing x $ SomeSing . SProved
  toSing (Disproved r) = withSomeSing r $ SomeSing . SDisproved

type family NatEqConsequences (a :: Nat) (b :: Nat) :: Type where
  NatEqConsequences Z      Z      = ()
  NatEqConsequences Z      (S _)  = Void
  NatEqConsequences (S _)  Z      = Void
  NatEqConsequences (S k1) (S k2) = k1 :~: k2
$(genDefunSymbols [''NatEqConsequences])

type WhyNatEqConsequencesSame (a :: Nat) = NatEqConsequences a a
$(genDefunSymbols [''WhyNatEqConsequencesSame])

type WhyDecEqZ (k :: Nat) = Decision (Z :~: k)
$(genDefunSymbols [''WhyDecEqZ])

type WhyDecEqS (n :: Nat) (k :: Nat) = Decision (S n :~: k)
$(genDefunSymbols [''WhyDecEqS])

-- The newtype wrapper is needed to work around
-- https://github.com/goldfirere/singletons/issues/198
newtype WhyDecEqNat (k :: Nat) = WhyDecEqNat
  { runWhyDecEqNat :: forall (j :: Nat). Sing j -> Decision (k :~: j) }

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
