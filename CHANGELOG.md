### next [????.??.??]
* Add `Data.Eliminator.TypeLits`, which re-exports
  `Data.Eliminator.TypeNats.elimNat` and adds a new `elimSymbol` eliminator
  for `GHC.TypeLits.Symbol`.

## 0.9 [2021.10.31]
* Require `singletons-base-3.1` and GHC 9.2.
* Add `{e,E}limProxy` to `Data.Eliminator`.
* `Data.Eliminator` no longer exports `{e,E}limFirst` and `{e,E}limLast`
  eliminators. If you wish to use eliminators that work over `First`/`Last`
  from `Data.Monoid`, you must import them `Data.Eliminator.Monoid`. If you
  wish to use eliminators that over `First`/`Last` from `Data.Semigroup`, you
  must import them from the new `Data.Eliminator.Semigroup` module.
* `Data.Eliminator` no longer exports `{e,E}limProduct` and `{e,E}limSum`
  eliminators. If you wish to use eliminators that work over `Product`/`Sum`
  from `Data.Monoid` or `Data.Semigroup`, you must import them
  `Data.Eliminator.Monoid` or `Data.Eliminator.Semigroup`. If you wish to use
  eliminators that over `Product`/`Sum` from
  `Data.Functor.Product`/`Data.Functor.Sum`, you must import them from the new
  `Data.Eliminator.Functor` module.

## 0.8 [2021.03.12]
* Require `singletons-base-3.0` and GHC 9.0.
* Remove eliminators for `Data.Semigroup.Option`, which is deprecated as of
  `base-4.15.0.0`.

## 0.7 [2020.03.25]
* Require `singletons-2.7` and GHC 8.10.
* Add experimental support for generating type-level eliminators through the
  `deriveTypeElim` and `deriveTypeElimNamed` functions.
* Add eliminators for `All`, `Any`, `Arg`, `Const`, `Down`, `Dual`, `First`,
  `Identity`, `Last`, `Max`, `Min`, `Option`, `Product`, `Sum`,
  and `WrappedMonoid`.

## 0.6 [2019.08.27]
* Require `singletons-2.6` and GHC 8.8.

### 0.5.1 [2019.04.26]
* Support `th-abstraction-0.3.0.0` or later.

## 0.5 [2018.09.18]
* Require `singletons-2.5` and GHC 8.6.

### 0.4.1 [2018.02.13]
* Add `elimVoid` to `Data.Eliminator`.

## 0.4 [2018.01.09]
* Require `singletons-2.4` and GHC 8.4.

## 0.3 [2017-11-07]
* Migrate the old `elimNat` from `Data.Eliminator` (which worked over the `Nat`
  from `GHC.TypeNats`) to `Data.Eliminator.TypeNats`. There `elimNat` that now
  lives in `Data.Eliminator` is for an unrelated `Nat` data type from the
  `singleton-nats` package (which is a proper, inductively defined, Peano
  natural number type).

## 0.2 [2017-07-22]
* Introduce the `Data.Eliminator.TH` module, which provides functionality for
  generating eliminator functions using Template Haskell. Currently, only
  simple algebraic data types that do not use polymorphic recursion are
  supported.
* All eliminators now use predicates with `(~>)`.

## 0.1 [2017-07-02]
* Initial release.
