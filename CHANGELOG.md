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
