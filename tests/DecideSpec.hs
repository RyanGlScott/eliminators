{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module DecideSpec where

import Data.Eliminator
import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.TH hiding (Decision(..))
import Data.Type.Equality

import EqualitySpec (cong, replace)
import DecideTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  let proved    = "Proved Refl"
      disproved = "Disproved <void>"
  describe "decEqNat" $ do
    it "returns evidence that two Nats are equal" $ do
      show (decEqNat (sLit @0) (sLit @0)) `shouldBe` proved
      show (decEqNat (sLit @1) (sLit @0)) `shouldBe` disproved
      show (decEqNat (sLit @0) (sLit @1)) `shouldBe` disproved
      show (decEqNat (sLit @1) (sLit @1)) `shouldBe` proved
  describe "decEqList" $ do
    it "returns evidence that two lists are equal" $ do
      let decEqNatList = decEqList decEqNat
      show (decEqNatList SNil                   SNil)                   `shouldBe` proved
      show (decEqNatList (SCons (sLit @0) SNil) SNil)                   `shouldBe` disproved
      show (decEqNatList SNil                   (SCons (sLit @0) SNil)) `shouldBe` disproved
      show (decEqNatList (SCons (sLit @0) SNil) (SCons (sLit @0) SNil)) `shouldBe` proved
      show (decEqNatList (SCons (sLit @1) SNil) (SCons (sLit @0) SNil)) `shouldBe` disproved

-----

peanoEqConsequencesSame :: forall (n :: Nat). Sing n -> NatEqConsequences n n
peanoEqConsequencesSame sn = elimNat @WhyNatEqConsequencesSameSym0 @n sn base step
  where
    base :: WhyNatEqConsequencesSame Z
    base = ()

    step :: forall (k :: Nat).
            Sing k
         -> WhyNatEqConsequencesSame k
         -> WhyNatEqConsequencesSame (S k)
    step _ _ = Refl

useNatEq :: forall n j. Sing n -> n :~: j -> NatEqConsequences n j
useNatEq sn nEqJ = replace @Nat @n @j @(NatEqConsequencesSym1 n)
                             (peanoEqConsequencesSame @n sn) nEqJ

zNotS :: forall n. Z :~: S n -> Void
zNotS = useNatEq @Z @(S n) SZ

sNotZ :: forall n. S n :~: Z -> Void
sNotZ eq = zNotS @n (sym eq)

sInjective :: forall n j. Sing n -> S n :~: S j -> n :~: j
sInjective sn = useNatEq @(S n) @(S j) (SS sn)

decEqZ :: forall (j :: Nat). Sing j -> Decision (Z :~: j)
decEqZ sj = elimNat @WhyDecEqZSym0 @j sj base step
  where
    base :: Decision (Z :~: Z)
    base = Proved Refl

    step :: forall (k :: Nat).
            Sing k -> Decision (Z :~: k) -> Decision (Z :~: S k)
    step _ _ = Disproved (zNotS @k)

decCongS :: forall n j. Sing n -> Decision (n :~: j) -> Decision (S n :~: S j)
decCongS sn dNJ = withSomeSing dNJ $ \(sDNJ :: Sing d) ->
                    elimDecision @_ @(ConstSym1 (Decision (S n :~: S j))) @d
                      sDNJ left right
  where
    left :: forall (x :: n :~: j).
            Sing x -> Decision (S n :~: S j)
    left yes = Proved $ cong @Nat @Nat @(TyCon S) @n @j (fromSing yes)

    right :: forall (r :: (n :~: j) ~> Void).
             Sing r -> Decision (S n :~: S j)
    right no = Disproved $ fromSing no . sInjective @n @j sn

decEqNat :: forall (n :: Nat) (j :: Nat). Sing n -> Sing j -> Decision (n :~: j)
decEqNat sn = runWhyDecEqNat (elimNat @(TyCon WhyDecEqNat) @n sn base step)
  where
    base :: WhyDecEqNat Z
    base = WhyDecEqNat decEqZ

    step :: forall (k :: Nat).
            Sing k
         -> WhyDecEqNat k
         -> WhyDecEqNat (S k)
    step sk swhyK = WhyDecEqNat $ \(sl :: Sing l) ->
                      elimNat @(WhyDecEqSSym1 k) @l sl baseStep stepStep
      where
        baseStep :: Decision (S k :~: Z)
        baseStep = Disproved $ sNotZ @k

        stepStep :: forall (m :: Nat).
                    Sing m
                 -> Decision (S k :~: m)
                 -> Decision (S k :~: S m)
        stepStep sm _ = decCongS sk (runWhyDecEqNat swhyK sm)

listEqConsequencesSame :: forall (es :: [e]). Sing es -> ListEqConsequences es es
listEqConsequencesSame sl = elimList @e @WhyListEqConsequencesSameSym0 @es sl base step
  where
    base :: ListEqConsequences '[] '[]
    base = ()

    step :: forall (x :: e) (xs :: [e]).
            Sing x -> Sing xs
         -> ListEqConsequences xs xs
         -> ListEqConsequences (x:xs) (x:xs)
    step _ _ _ = (Refl, Refl)

useListEq :: forall (xs :: [e]) (ys :: [e]).
             Sing xs -> xs :~: ys -> ListEqConsequences xs ys
useListEq sxs xsEqYs = replace @[e] @xs @ys @(ListEqConsequencesSym1 xs)
                               (listEqConsequencesSame @e @xs sxs) xsEqYs

nilNotCons :: forall (x :: e) (xs :: [e]). '[] :~: (x:xs) -> Void
nilNotCons = useListEq @e @'[] @(x:xs) SNil

consNotNil :: forall (x :: e) (xs :: [e]). (x:xs) :~: '[] -> Void
consNotNil eq = nilNotCons @e @x @xs (sym eq)

consInjective :: forall (x :: e) (xs :: [e]) (y :: e) (ys :: [e]).
                 Sing x -> Sing xs
              -> (x:xs) :~: (y:ys)
              -> (x :~: y, xs :~: ys)
consInjective sx sxs = useListEq @e @(x:xs) @(y:ys) (SCons sx sxs)

decEqNil :: forall (es :: [e]). Sing es -> Decision ('[] :~: es)
decEqNil ses = elimList @e @WhyDecEqNilSym0 @es ses base step
  where
    base :: Decision ('[] :~: '[])
    base = Proved Refl

    step :: forall (x :: e) (xs :: [e]).
            Sing x -> Sing xs
         -> Decision ('[] :~: xs)
         -> Decision ('[] :~: (x:xs))
    step _ _ _ = Disproved (nilNotCons @e @x @xs)

intermixListEqs :: forall (x :: e) (xs :: [e]) (y :: e) (ys :: [e]).
                   x :~: y -> xs :~: ys
                -> (x:xs) :~: (y:ys)
intermixListEqs xEqY xsEqYs =
  replace @e @x @y @(WhyIntermixListEqs1Sym3 x xs ys)
          (replace @[e] @xs @ys @(WhyIntermixListEqs2Sym2 x xs) Refl xsEqYs)
          xEqY

decCongCons :: forall (x :: e) (xs :: [e]) (y :: e) (ys :: [e]).
               Sing x -> Sing xs
            -> Decision (x :~: y) -> Decision (xs :~: ys)
            -> Decision ((x:xs) :~: (y:ys))
decCongCons sx sxs dXY dXsYs =
  withSomeSing dXY $ \(sDXY :: Sing dXY) ->
    elimDecision @_ @(ConstSym1 (Decision ((x:xs) :~: (y:ys)))) @dXY
      sDXY left right
  where
    left :: forall (z :: x :~: y).
            Sing z -> Decision ((x:xs) :~: (y:ys))
    left xEqY = withSomeSing dXsYs $ \(sDXsYs :: Sing dXsYs) ->
                  elimDecision @_ @(ConstSym1 (Decision ((x:xs) :~: (y:ys)))) @dXsYs
                    sDXsYs leftLeft leftRight
      where
        leftLeft :: forall (zz :: xs :~: ys).
                    Sing zz -> Decision ((x:xs) :~: (y:ys))
        leftLeft xsEqYs = Proved $ intermixListEqs (fromSing xEqY) (fromSing xsEqYs)

        leftRight :: forall (r :: (xs :~: ys) ~> Void).
                     Sing r -> Decision ((x:xs) :~: (y:ys))
        leftRight no = Disproved $ fromSing no . snd . injective

    right :: forall (r :: (x :~: y) ~> Void).
             Sing r -> Decision ((x:xs) :~: (y:ys))
    right no = Disproved $ fromSing no . fst . injective

    injective :: (x:xs) :~: (y:ys) -> (x :~: y, xs :~: ys)
    injective = consInjective @e @x @xs @y @ys sx sxs

decEqList :: forall (es1 :: [e]) (es2 :: [e]).
             (forall (e1 :: e) (e2 :: e).
                     Sing e1 -> Sing e2 -> Decision (e1 :~: e2))
          -> Sing es1 -> Sing es2 -> Decision (es1 :~: es2)
decEqList f ses1 = runWhyDecEqList (elimList @e @(TyCon1 WhyDecEqList) @es1 ses1 base step)
  where
    base :: WhyDecEqList '[]
    base = WhyDecEqList decEqNil

    step :: forall (x :: e) (xs :: [e]).
            Sing x -> Sing xs
         -> WhyDecEqList xs
         -> WhyDecEqList (x:xs)
    step sx sxs swhyXs = WhyDecEqList $ \(sl :: Sing l) ->
                           elimList @e @(WhyDecEqConsSym2 x xs) @l sl
                             stepBase stepStep
      where
        stepBase :: Decision ((x:xs) :~: '[])
        stepBase = Disproved $ consNotNil @e @x @xs

        stepStep :: forall (y :: e) (ys :: [e]).
                    Sing y -> Sing ys
                 -> Decision ((x:xs) :~: ys)
                 -> Decision ((x:xs) :~: (y:ys))
        stepStep sy sys _ = decCongCons sx sxs
                                        (f sx sy)
                                        (runWhyDecEqList swhyXs sys)
