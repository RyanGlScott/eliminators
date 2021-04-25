{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
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
module DecideTypes where

import Data.Eliminator
import Data.Kind
import Data.Nat
import Data.Singletons.TH hiding (Decision(..))

import Prelude.Singletons

-- Due to https://github.com/goldfirere/singletons/issues/82, promoting the
-- Decision data type from Data.Singletons.Decide is a tad awkward. To work
-- around these, we define a more general Decision' data type here.
type Decision' :: (Type ~> Type ~> Type) -> Type -> Type
data Decision' p a
  = Proved a
  | Disproved (p @@ a @@ Void)

elimDecision :: forall a (p :: PDecision a ~> Type) (d :: PDecision a).
                Sing d
             -> (forall (yes :: a). Sing yes -> p @@ Proved yes)
             -> (forall (no :: a ~> Void). Sing no -> p @@ Disproved no)
             -> p @@ d
elimDecision sd pProved pDisproved = go @d sd
  where
    go :: forall (d' :: PDecision a). Sing d' -> p @@ d'
    go (SProved yes)   = pProved yes
    go (SDisproved no) = pDisproved no

type ElimDecision :: forall a.
                     forall (p :: PDecision a ~> Type)
                            (d :: PDecision a) ->
                     (forall (yes :: a) -> p @@ Proved yes)
                  -> (forall (no :: a ~> Void) -> p @@ Disproved no)
                  -> p @@ d
type family ElimDecision p d pProved pDisproved where
  forall a (p :: PDecision a ~> Type)
         (pProved    :: forall (yes :: a) -> p @@ Proved yes)
         (pDisproved :: forall (no :: a ~> Void) -> p @@ Disproved no) yes.
    ElimDecision p (Proved yes) pProved pDisproved = pProved yes
  forall a (p :: PDecision a ~> Type)
         (pProved    :: forall (yes :: a) -> p @@ Proved yes)
         (pDisproved :: forall (no :: a ~> Void) -> p @@ Disproved no) no.
    ElimDecision p (Disproved no) pProved pDisproved = pDisproved no

instance Show a => Show (Decision' p a) where
  showsPrec p (Proved a) =
    showParen (p > 10) $ showString "Proved " . showsPrec 11 a
  showsPrec p (Disproved _) =
    showParen (p > 10) $ showString "Disproved <void>"

type Decision :: Type -> Type
type Decision  = Decision' (TyCon (->))

type PDecision :: Type -> Type
type PDecision = Decision' (~>@#@$)

type SDecision :: PDecision a -> Type
data SDecision d where
  SProved    :: forall a (x :: a).         Sing x -> SDecision (Proved x)
  SDisproved :: forall a (r :: a ~> Void). Sing r -> SDecision (Disproved r)
type instance Sing = SDecision

instance SingKind a => SingKind (PDecision a) where
  type Demote (PDecision a) = Decision (Demote a)
  fromSing (SProved a)    = Proved (fromSing a)
  fromSing (SDisproved r) = Disproved (fromSing r)
  toSing (Proved x)    = withSomeSing x $ SomeSing . SProved
  toSing (Disproved r) = withSomeSing r $ SomeSing . SDisproved

-----

-- These newtype wrappers are needed to work around
-- https://gitlab.haskell.org/ghc/ghc/issues/9269
type WhyDecEqNat :: Nat -> Type
newtype WhyDecEqNat k = WhyDecEqNat
  { runWhyDecEqNat :: forall (j :: Nat). Sing j -> Decision (k :~: j) }

type WhyDecEqList :: [e] -> Type
newtype WhyDecEqList (l1 :: [e]) = WhyDecEqList
  { runWhyDecEqList :: forall (l2 :: [e]). Sing l2 -> Decision (l1 :~: l2) }

$(singletons [d|
  type ConstVoidNat :: forall (m :: Nat) -> Const Type m -> Const Type (S m)
  type ConstVoidNat m r = Void

  type EqSameNat :: Nat -> forall (m :: Nat) -> Const Type m -> Const Type (S m)
  type EqSameNat n m r = n :~: m

  type ConstVoidList :: forall e. forall (y :: e) (ys :: [e])
                     -> Const Type ys -> Const Type (y:ys)
  type ConstVoidList y ys r = Void

  type EqSameList :: forall e. e -> [e] -> forall (y :: e) (ys :: [e])
                  -> Const Type ys -> Const Type (y:ys)
  type EqSameList x xs y ys r = (x :~: y, xs :~: ys)
  |])

$(singletons [d|
  type NatEqConsequencesBase :: Nat -> Type
  type NatEqConsequencesBase m = ElimNat (ConstSym1 Type) m () ConstVoidNatSym1

  type NatEqConsequencesStep :: forall (m :: Nat) -> Const (Nat ~> Type) m
                             -> Nat -> Const Type (S m)
  type NatEqConsequencesStep m r n = ElimNat (ConstSym1 Type) n Void (EqSameNatSym2 m)

  type ListEqConsequencesBase :: [e] -> Type
  type ListEqConsequencesBase ys = ElimList (ConstSym1 Type) ys () ConstVoidListSym2

  type ListEqConsequencesStep :: forall e. forall (x :: e) (xs :: [e])
                              -> Const ([e] ~> Type) xs -> [e] -> Const Type (x:xs)
  type ListEqConsequencesStep x xs r ys = ElimList (ConstSym1 Type) ys Void (EqSameListSym4 x xs)
  |])

$(singletons [d|
  type NatEqConsequences :: Nat -> Nat -> Type
  type NatEqConsequences n m =
    ElimNat (ConstSym1 (Nat ~> Type)) n
            NatEqConsequencesBaseSym0
            NatEqConsequencesStepSym1 @@ m

  type WhyNatEqConsequencesSame :: Nat -> Type
  type WhyNatEqConsequencesSame a = NatEqConsequences a a

  type WhyDecEqZ :: Nat -> Type
  type WhyDecEqZ k = Decision (Z :~: k)

  type WhyDecEqS :: Nat -> Nat -> Type
  type WhyDecEqS n k = Decision (S n :~: k)

  type ListEqConsequences :: [e] -> [e] -> Type
  type ListEqConsequences (xs :: [e]) (ys :: [e]) =
    ElimList (ConstSym1 ([e] ~> Type)) xs
             ListEqConsequencesBaseSym0
             ListEqConsequencesStepSym2 @@ ys

  type WhyListEqConsequencesSame :: [e] -> Type
  type WhyListEqConsequencesSame es = ListEqConsequences es es

  type WhyDecEqNil :: [e] -> Type
  type WhyDecEqNil es = Decision ('[] :~: es)

  type WhyDecEqCons :: e -> [e] -> [e] -> Type
  type WhyDecEqCons x xs es = Decision ((x:xs) :~: es)

  type WhyIntermixListEqs1 :: e -> [e] -> [e] -> e -> Type
  type WhyIntermixListEqs1 x xs ys k = (x:xs) :~: (k:ys)

  type WhyIntermixListEqs2 :: e -> [e] -> [e] -> Type
  type WhyIntermixListEqs2 x xs k = (x:xs) :~: (x:k)
  |])
