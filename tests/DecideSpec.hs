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
import Data.Singletons.Prelude
import Data.Singletons.TH hiding (Decision(..))
import Data.Type.Equality

import EqualitySpec (cong, replace)
import DecideTypes
import PeanoTypes

import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = parallel $ do
  let proved    = "Proved Refl"
      disproved = "Disproved <void>"
  describe "decEqPeano" $ do
    it "returns evidence that two Peanos are equal" $ do
      show (decEqPeano SZ      SZ)      `shouldBe` proved
      show (decEqPeano (SS SZ) SZ)      `shouldBe` disproved
      show (decEqPeano SZ      (SS SZ)) `shouldBe` disproved
      show (decEqPeano (SS SZ) (SS SZ)) `shouldBe` proved
  describe "decEqList" $ do
    it "returns evidence that two lists are equal" $ do
      let decEqPeanoList = decEqList decEqPeano
      show (decEqPeanoList SNil                 SNil)            `shouldBe` proved
      show (decEqPeanoList (SCons SZ SNil)      SNil)            `shouldBe` disproved
      show (decEqPeanoList SNil                 (SCons SZ SNil)) `shouldBe` disproved
      show (decEqPeanoList (SCons SZ SNil)      (SCons SZ SNil)) `shouldBe` proved
      -- TODO: Try this in the next version of singletons
      -- show (decEqPeanoList (SCons (SS SZ) SNil) (SCons SZ SNil)) `shouldBe` disproved

-----

peanoEqConsequencesSame :: forall (n :: Peano). Sing n -> PeanoEqConsequences n n
peanoEqConsequencesSame sn = elimPeano @WhyPeanoEqConsequencesSameSym0 @n sn base step
  where
    base :: WhyPeanoEqConsequencesSame Z
    base = ()

    step :: forall (k :: Peano).
            Sing k
         -> WhyPeanoEqConsequencesSame k
         -> WhyPeanoEqConsequencesSame (S k)
    step _ _ = Refl

usePeanoEq :: forall n j. Sing n -> n :~: j -> PeanoEqConsequences n j
usePeanoEq sn nEqJ = replace @Peano @n @j @(PeanoEqConsequencesSym1 n)
                             (peanoEqConsequencesSame @n sn) nEqJ

zNotS :: forall n. Z :~: S n -> Void
zNotS = usePeanoEq @Z @(S n) SZ

sNotZ :: forall n. S n :~: Z -> Void
sNotZ eq = zNotS @n (sym eq)

sInjective :: forall n j. Sing n -> S n :~: S j -> n :~: j
sInjective sn = usePeanoEq @(S n) @(S j) (SS sn)

decEqZ :: forall (j :: Peano). Sing j -> Decision (Z :~: j)
decEqZ sj = elimPeano @WhyDecEqZSym0 @j sj base step
  where
    base :: Decision (Z :~: Z)
    base = Proved Refl

    step :: forall (k :: Peano).
            Sing k -> Decision (Z :~: k) -> Decision (Z :~: S k)
    step _ _ = Disproved (zNotS @k)

decCongS :: forall n j. Sing n -> Decision (n :~: j) -> Decision (S n :~: S j)
decCongS sn dNJ = withSomeSing dNJ $ \(sDNJ :: Sing d) ->
                    elimDecision @_ @(ConstSym1 (Decision (S n :~: S j))) @d
                      sDNJ left right
  where
    left :: forall (x :: n :~: j).
            Sing x -> Decision (S n :~: S j)
    left yes = Proved $ cong @Peano @Peano @(TyCon1 S) @n @j (fromSing yes)

    right :: forall (r :: (n :~: j) ~> Void).
             Sing r -> Decision (S n :~: S j)
    right no = Disproved $ fromSing no . sInjective @n @j sn

decEqPeano :: forall (n :: Peano) (j :: Peano). Sing n -> Sing j -> Decision (n :~: j)
decEqPeano sn = runWhyDecEqPeano (elimPeano @(TyCon1 WhyDecEqPeano) @n sn base step)
  where
    base :: WhyDecEqPeano Z
    base = WhyDecEqPeano decEqZ

    step :: forall (k :: Peano).
            Sing k
         -> WhyDecEqPeano k
         -> WhyDecEqPeano (S k)
    step sk swhyK = WhyDecEqPeano $ \(sl :: Sing l) ->
                      elimPeano @(WhyDecEqSSym1 k) @l sl baseStep stepStep
      where
        baseStep :: Decision (S k :~: Z)
        baseStep = Disproved $ sNotZ @k

        stepStep :: forall (m :: Peano).
                    Sing m
                 -> Decision (S k :~: m)
                 -> Decision (S k :~: S m)
        stepStep sm _ = decCongS sk (runWhyDecEqPeano swhyK sm)

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
