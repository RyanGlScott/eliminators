{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module DecideTypes where

import Data.Eliminator
import Data.Kind
import Data.Nat
import Data.Singletons.TH hiding (Decision(..))

import Prelude.Singletons (ConstSym1)

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

type ConstVoidNat :: Nat -> Type -> Type
type ConstVoidNat m r = Void

-- ElimNat requires an argument of kind (forall (m :: Nat) -> ...), which is
-- not the same thing as (Nat -> ...). Unfortunately, it's not easy to convince
-- singletons-th to generate defunctionalization symbols for ConstVoidNat that
-- have a dependent kind like this. As a result, we have to define
-- defunctionalization symbols by hand with the appropriate kind.
type ConstVoidNatSym :: forall (m :: Nat) -> (Type ~> Type)
data ConstVoidNatSym m z
type instance Apply (ConstVoidNatSym m) r = ConstVoidNat m r

type EqSameNat :: Nat -> Nat -> Type -> Type
type EqSameNat n m r = n :~: m

type EqSameNatSym :: Nat -> forall (m :: Nat) -> (Type ~> Type)
data EqSameNatSym n m z
type instance Apply (EqSameNatSym n m) r = EqSameNat n m r

type ConstVoidList :: e -> [e] -> Type -> Type
type ConstVoidList y ys r = Void

type ConstVoidListSym :: forall e. forall (y :: e) (ys :: [e])
                      -> (Type ~> Type)
data ConstVoidListSym y ys z
type instance Apply (ConstVoidListSym y ys) r = ConstVoidList y ys r

type EqSameList :: e -> [e] -> e -> [e] -> Type -> Type
type EqSameList x xs y ys r = (x :~: y, xs :~: ys)

type EqSameListSym :: forall e. e -> [e] -> forall (y :: e) (ys :: [e])
                   -> (Type ~> Type)
data EqSameListSym x xs y ys z
type instance Apply (EqSameListSym x xs y ys) r = EqSameList x xs y ys r

$(singletons [d|
  type NatEqConsequencesBase :: Nat -> Type
  type NatEqConsequencesBase m = ElimNat (ConstSym1 Type) m () ConstVoidNatSym

  type NatEqConsequencesStep :: Nat -> (Nat ~> Type) -> Nat -> Type
  type NatEqConsequencesStep m r n = ElimNat (ConstSym1 Type) n Void (EqSameNatSym m)

  type ListEqConsequencesBase :: [e] -> Type
  type ListEqConsequencesBase ys = ElimList (ConstSym1 Type) ys () ConstVoidListSym

  type ListEqConsequencesStep :: e -> [e] -> ([e] ~> Type) -> [e] -> Type
  type ListEqConsequencesStep x xs r ys = ElimList (ConstSym1 Type) ys Void (EqSameListSym x xs)
  |])

type NatEqConsequencesStepSym :: forall (m :: Nat)
                              -> (Nat ~> Type) ~> (Nat ~> Type)
data NatEqConsequencesStepSym m z
type instance Apply (NatEqConsequencesStepSym m) r = NatEqConsequencesStepSym2 m r

type ListEqConsequencesStepSym :: forall e. forall (x :: e) (xs :: [e])
                               -> ([e] ~> Type) ~> ([e] ~> Type)
data ListEqConsequencesStepSym x xs z
type instance Apply (ListEqConsequencesStepSym x xs) r = ListEqConsequencesStepSym3 x xs r

$(singletons [d|
  type NatEqConsequences :: Nat -> Nat -> Type
  type NatEqConsequences n m =
    ElimNat (ConstSym1 (Nat ~> Type)) n
            NatEqConsequencesBaseSym0
            NatEqConsequencesStepSym @@ m

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
             ListEqConsequencesStepSym @@ ys

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
