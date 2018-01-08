## next [????.??.??]
* Require GHC 8.4.

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
