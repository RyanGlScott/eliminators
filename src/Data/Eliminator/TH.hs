{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Unsafe #-}
{-|
Module:      Data.Eliminator.TH
Copyright:   (C) 2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Stability:   Experimental
Portability: GHC

Generate dependently typed elimination functions using Template Haskell.
-}
module Data.Eliminator.TH (
    -- * Eliminator generation
    -- ** Term-level eliminators
    -- $term-conventions
    deriveElim
  , deriveElimNamed
    -- ** Type-level eliminators
    -- $type-conventions
  , deriveTypeElim
  , deriveTypeElimNamed
  ) where

import           Control.Applicative
import           Control.Monad

import           Data.Char (isLetter, isUpper, toUpper)
import           Data.Foldable
import qualified Data.Kind as Kind (Type)
import           Data.Maybe
import           Data.Proxy
import           Data.Singletons.Prelude
import           Data.Singletons.TH.Options

import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Language.Haskell.TH.Desugar hiding (NewOrData(..))

{- $term-conventions
'deriveElim' and 'deriveElimNamed' provide a way to automate the creation of
eliminator functions, which are mostly boilerplate. Here is a complete example
showing how one might use 'deriveElim':

@
$('singletons' [d| data MyList a = MyNil | MyCons a (MyList a) |])
$('deriveElim' ''MyList)
@

This will produce an eliminator function that looks roughly like the following:

@
elimMyList :: forall (a :: 'Type') (p :: MyList a '~>' 'Type') (l :: MyList a).
              'Sing' l
           -> 'Apply' p MyNil
           -> (forall (x :: a). 'Sing' x
                -> forall (xs :: MyList a). 'Sing' xs -> 'Apply' p xs
                -> 'Apply' p (MyCons x xs))
           -> 'Apply' p l
elimMyList SMyNil pMyNil _ = pMyNil
elimMyList (SMyCons (x' :: 'Sing' x) (xs' :: 'Sing' xs)) pMyNil pMyCons
  = pMyCons x' xs' (elimMyList \@a \@p \@xs pMyNil pMyCons)
@

There are some important things to note here:

* Because these eliminators use 'Sing' under the hood, in order for
  'deriveElim' to work, the 'Sing' instance for the data type given as an
  argument must be in scope. Moreover, 'deriveElim' assumes the naming
  conventions for singled constructors used by the @singletons@ library.
  (This is why the 'singletons' function is used in the example above).

* There is a convention for the order in which the arguments appear.
  The quantified type variables appear in this order:

    1. First, the type variables of the data type itself (@a@, in the above example).

    2. Second, a predicate type variable of kind @\<Datatype\> '~>' 'Type'@
       (@p@, in the above example).

    3. Finally, a type variable of kind @\<Datatype\>@ (@l@, in the above example).

  The function arguments appear in this order:

    1. First, a 'Sing' argument (@'Sing' l@, in the above example).

    2. Next, there are arguments that correspond to each constructor. More on this
       in a second.

  The return type is the predicate type variable applied to the data type
  (@'Apply' p (MyCons x xs)@, the above example).

  The type of each constructor argument also follows certain conventions:

    1. For each field, there will be a rank-2 type variable whose kind matches
       the type of the field, followed by a matching 'Sing' type. For instance,
       in the above example, @forall (x :: a). 'Sing' x@ corresponds to the
       first field of @MyCons@.

    2. In addition, if the field is a recursive occurrence of the data type,
       an additional argument will follow the 'Sing' type. This is best
       explained using the above example. In the @MyCons@ constructor, the second
       field (of type @MyCons a@) is a recursive occurrence of @MyCons@, so
       that corresponds to the type
       @forall (xs :: MyList a). 'Sing' xs -> 'Apply' p xs@, where @'Apply' p xs@
       is only present due to the recursion.

    3. Finally, the return type will be the predicate type variable applied
       to a saturated occurrence of the data constructor
       (@'Apply' p (MyCons x xs)@, in the above example).

* You'll need to enable lots of GHC extensions in order for the code generated
  by 'deriveElim' to typecheck. You'll need at least the following:

    * @AllowAmbiguousTypes@

    * @DataKinds@

    * @GADTs@

    * @PolyKinds@

    * @RankNTypes@

    * @ScopedTypeVariables@

    * @TemplateHaskell@

    * @TypeApplications@

* 'deriveElim' doesn't support every possible data type at the moment.
  It is known not to work for the following:

    * Data types defined using @GADTs@ or @ExistentialQuantification@

    * Data family instances

    * Data types which use polymorphic recursion
      (e.g., @data Foo a = Foo (Foo a)@)
-}

-- | @'deriveElim' dataName@ generates a top-level elimination function for the
-- datatype @dataName@. The eliminator will follow these naming conventions:
--
-- * If the datatype has an alphanumeric name, its eliminator will have that name
--   with @elim@ prepended.
--
-- * If the datatype has a symbolic name, its eliminator will have that name
--   with @~>@ prepended.
deriveElim :: Name -> Q [Dec]
deriveElim dataName = deriveElimNamed (eliminatorName dataName) dataName

-- | @'deriveElimNamed' funName dataName@ generates a top-level elimination
-- function named @funName@ for the datatype @dataName@.
deriveElimNamed :: String -> Name -> Q [Dec]
deriveElimNamed = deriveElimNamed' (Proxy @IsTerm)

{- $type-conventions
'deriveTypeElim' and 'deriveTypeElimNamed' are like 'deriveElim' and
'deriveElimNamed' except that they create /type/-level eliminators instead of
term-level ones. Here is an example showing how one might use
'deriveTypeElim':

@
data MyList a = MyNil | MyCons a (MyList a)
$('deriveTypeElim' ''MyList)
@

This will produce an eliminator function that looks roughly like the following:

@
type ElimMyList :: forall (a :: 'Type').
                   forall (p :: MyList a '~>' 'Type') (l :: MyList a)
                -> 'Apply' p MyNil
                -> (forall (x :: a) (xs :: MyList a)
                     -> 'Apply' p xs '~>' 'Apply' p (MyCons x xs))
                -> 'Apply' p l
type family ElimMyList p l pMyNil pMyCons where
  forall (a :: 'Type')
         (p :: MyList a ~> 'Type')
         (pMyNil :: 'Apply' p MyNil)
         (pMyCons :: forall (x :: a) (xs :: MyList a)
                      -> 'Apply' p xs '~>' 'Apply' p (MyCons x xs)).
    ElimMyList @a p MyNil pMyNil pMyCons =
      pMyNil
  forall (a :: 'Type')
         (p :: MyList a ~> 'Type')
         (_pMyNil :: 'Apply' p MyNil)
         (pMyCons :: forall (x :: a) (xs :: MyList a)
                      -> 'Apply' p xs '~>' 'Apply' p (MyCons x xs))
         x' xs'.
    ElimMyList @a p (MyCons x' xs') pMyNil pMyCons =
      'Apply' (pMyCons x' xs') (ElimMyList @a p xs' pMyNil pMyCons)
@

Note the following differences from a term-level eliminator that 'deriveElim'
would generate:

* Type-level eliminators do not use 'Sing'. Instead, they use visible dependent
  quantification. That is, instead of generating
  @forall (x :: a). Sing x -> ...@ (as a term-level eliminator would do), a
  type-level eliminator would use @forall (x :: a) -> ...@.

* Term-level eliminators quantify @p@ with an invisible @forall@, whereas
  type-level eliminators quantify @p@ with a visible @forall@. (Really, @p@
  ought to be quantified visibly in both forms of eliminator, but GHC does not
  yet support visible dependent quantification at the term level.)

* Type-level eliminators use ('~>') in certain places where (@->@) would appear
  in term-level eliminators. For instance, note the use of
  @'Apply' p xs '~>' 'Apply' p (MyCons x xs)@ in @ElimMyList@ above. This is
  done to make it easier to use type-level eliminators with defunctionalization
  symbols (which aren't necessary for term-level eliminators).

  This comes with a notable drawback: type-level eliminators cannot support
  data constructors where recursive occurrences of the data type appear in a
  position other than the last field of a constructor. In other words,
  'deriveTypeElim' works on the @MyList@ example above, but not this variant:

  @
  data SnocList a = SnocNil | SnocCons (SnocList a) a
  @

  This is because @$('deriveTypeElim' ''SnocList)@ would generate an eliminator
  with the following kind:

  @
  type ElimSnocList :: forall (a :: 'Type').
                       forall (p :: SnocList a '~>' 'Type') (l :: SnocList a)
                    -> 'Apply' p SnocNil
                    -> (forall (xs :: SnocList a) -> 'Apply' p xs
                          '~>' (forall (x :: a) -> 'Apply' p (SnocCons x xs)))
                    -> 'Apply' p l
  @

  Unfortunately, the kind
  @'Apply' p xs '~>' (forall (x :: a) -> 'Apply' p (SnocCons x xs))@ is
  impredicative.

* In addition to the language extensions that 'deriveElim' requires, you'll need
  to enable these extensions in order to use 'deriveTypeElim':

    * @StandaloneKindSignatures@

    * @UndecidableInstances@
-}

-- | @'deriveTypeElim' dataName@ generates a type-level eliminator for the
-- datatype @dataName@. The eliminator will follow these naming conventions:
--
-- * If the datatype has an alphanumeric name, its eliminator will have that name
--   with @Elim@ prepended.
--
-- * If the datatype has a symbolic name, its eliminator will have that name
--   with @~>@ prepended.
deriveTypeElim :: Name -> Q [Dec]
deriveTypeElim dataName = deriveTypeElimNamed (upcase (eliminatorName dataName)) dataName

-- | @'deriveTypeElimNamed' funName dataName@ generates a type-level eliminator
-- named @funName@ for the datatype @dataName@.
deriveTypeElimNamed :: String -> Name -> Q [Dec]
deriveTypeElimNamed = deriveElimNamed' (Proxy @IsType)

-- The workhorse for deriveElim(Named). This generates either a term- or
-- type-level eliminator, depending on which Eliminator instance is used.
deriveElimNamed' ::
     Eliminator t
  => proxy t
  -> String  -- The name of the eliminator function
  -> Name    -- The name of the data type
  -> Q [Dec] -- The eliminator's type signature and body
deriveElimNamed' prox funName dataName = do
  info@(DatatypeInfo { datatypeVars    = dataVarBndrs
                     , datatypeVariant = variant
                     , datatypeCons    = cons
                     }) <- reifyDatatype dataName
  let noDataFamilies =
        fail "Eliminators for data family instances are currently not supported"
  case variant of
    DataInstance    -> noDataFamilies
    NewtypeInstance -> noDataFamilies
    Datatype        -> pure ()
    Newtype         -> pure ()
  predVar <- newName "p"
  singVar <- newName "s"
  let elimName = mkName funName
      promDataKind = datatypeType info
      predVarBndr = KindedTV predVar (InfixT promDataKind ''(~>) (ConT ''Kind.Type))
      singVarBndr = KindedTV singVar promDataKind
  caseTypes <- traverse (caseType prox dataName predVar) cons
  let returnType  = predType predVar (VarT singVar)
      elimType    = elimTypeSig prox dataVarBndrs predVarBndr singVarBndr
                                caseTypes returnType
  elimEqns <- qElimEqns prox (mkName funName) dataName
                        dataVarBndrs predVarBndr singVarBndr
                        caseTypes cons
  pure [elimSigD prox elimName elimType, elimEqns]

-- Generate the type for a "case alternative" in an eliminator function's type
-- signature, which is done on a constructor-by-constructor basis.
caseType ::
     Eliminator t
  => proxy t
  -> Name            -- The name of the data type
  -> Name            -- The predicate type variable
  -> ConstructorInfo -- The data constructor
  -> Q Type          -- The full case type
caseType prox dataName predVar
         (ConstructorInfo { constructorName    = conName
                          , constructorVars    = conVars
                          , constructorContext = conContext
                          , constructorFields  = fieldTypes })
  = do unless (null conVars && null conContext) $
         fail $ unlines
           [ "Eliminators for GADTs or datatypes with existentially quantified"
           , "data constructors currently not supported"
           ]
       vars <- newNameList "f" $ length fieldTypes
       let returnType = predType predVar
                                 (foldl' AppT (ConT conName) (map VarT vars))
       pure $ foldr' (\(var, varType) t ->
                        prependElimCaseTypeVar prox dataName predVar var varType t)
                     returnType
                     (zip vars fieldTypes)

-- Generate a single clause for a term-level eliminator.
caseClause ::
     Name            -- The name of the eliminator function
  -> Name            -- The name of the data type
  -> [TyVarBndr]     -- The type variables bound by the data type
  -> TyVarBndr       -- The predicate type variable
  -> Int             -- The index of this constructor (0-indexed)
  -> Int             -- The total number of data constructors
  -> ConstructorInfo -- The data constructor
  -> Q Clause        -- The generated function clause
caseClause elimName dataName dataVarBndrs predVarBndr conIndex numCons
    (ConstructorInfo { constructorName   = conName
                     , constructorFields = fieldTypes })
  = do let numFields = length fieldTypes
       singVars    <- newNameList "s"   numFields
       singVarSigs <- newNameList "sTy" numFields
       usedCaseVar <- newName "useThis"
       caseVars    <- ireplicateA numCons $ \i ->
                        if i == conIndex
                        then pure usedCaseVar
                        else newName ("_p" ++ show i)
       let singConName = singledDataConName defaultOptions conName
           mkSingVarPat var varSig = SigP (VarP var) (singType varSig)
           singVarPats = zipWith mkSingVarPat singVars singVarSigs

           mbInductiveArg singVar singVarSig varType =
             let prefix = foldAppTypeE (VarE elimName)
                             $ map (VarT . tvName) dataVarBndrs
                            ++ [VarT (tvName predVarBndr), VarT singVarSig]
                 inductiveArg = foldAppE prefix
                                  $ VarE singVar:map VarE caseVars
             in mbInductiveCase dataName varType inductiveArg
           mkArg f (singVar, singVarSig, varType) =
             foldAppE f $ VarE singVar
                        : maybeToList (mbInductiveArg singVar singVarSig varType)
           rhs = foldl' mkArg (VarE usedCaseVar) $
                        zip3 singVars singVarSigs fieldTypes
       pure $ Clause (ConP singConName singVarPats : map VarP caseVars)
                     (NormalB rhs)
                     []

-- Generate a single equation for a type-level eliminator.
--
-- This code is fairly similar in structure to caseClause, but different
-- enough in subtle ways that I did not attempt to de-duplicate this code as
-- a method of the Eliminator class.
caseTySynEqn ::
     Name            -- The name of the eliminator function
  -> Name            -- The name of the data type
  -> [TyVarBndr]     -- The type variables bound by the data type
  -> TyVarBndr       -- The predicate type variable
  -> Int             -- The index of this constructor (0-indexed)
  -> [Type]          -- The types of each "case alternative" in the eliminator
                     -- function's type signature
  -> ConstructorInfo -- The data constructor
  -> Q TySynEqn      -- The generated type family equation
caseTySynEqn elimName dataName dataVarBndrs predVarBndr conIndex caseTypes
    (ConstructorInfo { constructorName   = conName
                     , constructorFields = fieldTypes })
  = do let dataVarNames = map tvName dataVarBndrs
           predVarName  = tvName predVarBndr
           numFields    = length fieldTypes
       singVars     <- newNameList "s" numFields
       usedCaseVar  <- newName "useThis"
       caseVarBndrs <- flip itraverse caseTypes $ \i caseTy ->
                         let mkVarName
                               | i == conIndex = pure usedCaseVar
                               | otherwise     = newName ("_p" ++ show i)
                         in liftA2 KindedTV mkVarName (pure caseTy)
       let caseVarNames = map tvName caseVarBndrs
           prefix       = foldAppKindT (ConT elimName) $ map VarT dataVarNames
           mbInductiveArg singVar varType =
             let inductiveArg = foldAppT prefix $ VarT predVarName
                                                : VarT singVar
                                                : map VarT caseVarNames
             in mbInductiveCase dataName varType inductiveArg
           mkArg f (singVar, varType) =
             foldAppDefunT (f `AppT` VarT singVar)
                         $ maybeToList (mbInductiveArg singVar varType)
           bndrs = dataVarBndrs ++ predVarBndr : caseVarBndrs ++ map PlainTV singVars
           lhs   = foldAppT prefix $ VarT predVarName
                                   : foldAppT (ConT conName) (map VarT singVars)
                                   : map VarT caseVarNames
           rhs   = foldl' mkArg (VarT usedCaseVar) $ zip singVars fieldTypes
       pure $ TySynEqn (Just bndrs) lhs rhs

-- Are we dealing with a term or a type?
data TermOrType
  = IsTerm
  | IsType

-- A class that abstracts out certain common operations that one must perform
-- for both term- and type-level eliminators.
class Eliminator (t :: TermOrType) where
  -- Create the Dec for an eliminator function's type signature.
  elimSigD ::
       proxy t
    -> Name -- The name of the eliminator function
    -> Type -- The type of the eliminator function
    -> Dec  -- The type signature Dec (SigD or KiSigD)

  -- Create an eliminator function's type.
  elimTypeSig ::
       proxy t
    -> [TyVarBndr] -- The type variables bound by the data type
    -> TyVarBndr   -- The predicate type variable
    -> TyVarBndr   -- The type variable whose kind is that of the data type itself
    -> [Type]      -- The types of each "case alternative" in the eliminator
                   -- function's type signature
    -> Type        -- The eliminator function's return type
    -> Type        -- The full type

  -- Take a data constructor's field type and prepend it to a "case
  -- alternative" in an eliminator function's type signature.
  prependElimCaseTypeVar ::
       proxy t
    -> Name -- The name of the data type
    -> Name -- The predicate type variable
    -> Name -- A fresh type variable name
    -> Kind -- The field type
    -> Type -- The rest of the "case alternative" type
    -> Type -- The "case alternative" type after prepending

  -- Generate the clauses/equations for the body of the eliminator function.
  qElimEqns ::
       proxy t
    -> Name              -- The name of the eliminator function
    -> Name              -- The name of the data type
    -> [TyVarBndr]       -- The type variables bound by the data type
    -> TyVarBndr         -- The predicate type variable
    -> TyVarBndr         -- The type variable whose kind is that of the data type itself
    -> [Type]            -- The types of each "case alternative" in the eliminator
                         -- function's type signature
    -> [ConstructorInfo] -- The data constructors
    -> Q Dec             -- The Dec containing the clauses/equations

instance Eliminator IsTerm where
  elimSigD _ = SigD

  elimTypeSig _ dataVarBndrs predVarBndr singVarBndr caseTypes returnType =
    ForallT (dataVarBndrs ++ [predVarBndr, singVarBndr]) [] $
    ravel (singType (tvName singVarBndr):caseTypes) returnType

  prependElimCaseTypeVar _ dataName predVar var varType t =
    ForallT [KindedTV var varType] [] $
    ravel (singType var:maybeToList (mbInductiveType dataName predVar var varType)) t

  qElimEqns _ elimName dataName dataVarBndrs predVarBndr _singVarBndr _caseTypes cons
    | null cons
    = do singVal <- newName "singVal"
         pure $ FunD elimName [Clause [VarP singVal]
                               (NormalB (CaseE (VarE singVal) [])) []]
    | otherwise
    = do caseClauses
           <- itraverse (\i -> caseClause elimName dataName
                               dataVarBndrs predVarBndr i (length cons)) cons
         pure $ FunD elimName caseClauses

instance Eliminator IsType where
  elimSigD _ = KiSigD

  elimTypeSig _ dataVarBndrs predVarBndr singVarBndr caseTypes returnType =
    ForallT dataVarBndrs [] $
    ForallVisT [predVarBndr, singVarBndr] $
    ravel caseTypes returnType

  prependElimCaseTypeVar _ dataName predVar var varType t =
    ForallVisT [KindedTV var varType] $
    ravelDefun (maybeToList (mbInductiveType dataName predVar var varType)) t

  qElimEqns _ elimName dataName dataVarBndrs predVarBndr singVarBndr caseTypes cons = do
    caseVarBndrs <- replicateM (length caseTypes) (PlainTV <$> newName "p")
    let predVar   = tvName predVarBndr
        singVar   = tvName singVarBndr
        tyFamHead = TypeFamilyHead elimName
                      (PlainTV predVar:PlainTV singVar:caseVarBndrs)
                      NoSig Nothing
    caseEqns <- itraverse (\i -> caseTySynEqn elimName dataName
                                 dataVarBndrs predVarBndr i caseTypes) cons
    pure $ ClosedTypeFamilyD tyFamHead caseEqns

mbInductiveType :: Name -> Name -> Name -> Kind -> Maybe Type
mbInductiveType dataName predVar var varType =
  mbInductiveCase dataName varType $ predType predVar $ VarT var

-- TODO: Rule out polymorphic recursion
mbInductiveCase :: Name -> Type -> a -> Maybe a
mbInductiveCase dataName varType inductiveArg
  = case unfoldType varType of
      (headTy, _)
          -- Annoying special case for lists
        | ListT <- headTy
        , dataName == ''[]
       -> Just inductiveArg

        | ConT n <- headTy
        , dataName == n
       -> Just inductiveArg

        | otherwise
       -> Nothing

-- | Construct a type of the form @'Sing' x@ given @x@.
singType :: Name -> Type
singType x = ConT ''Sing `AppT` VarT x

-- | Construct a type of the form @'Apply' p ty@ given @p@ and @ty@.
predType :: Name -> Type -> Type
predType p ty = ConT ''Apply `AppT` VarT p `AppT` ty

-- | Generate a list of fresh names with a common prefix, and numbered suffixes.
newNameList :: String -> Int -> Q [Name]
newNameList prefix n = ireplicateA n $ newName . (prefix ++) . show

-- Compute an eliminator function's name from the data type name.
eliminatorName :: Name -> String
eliminatorName n
  | first:_ <- nStr
  , isUpper first
  = "elim" ++ nStr

  | otherwise
  = "~>" ++ nStr
  where
    nStr = nameBase n

-- Construct a function type, separating the arguments with ->
ravel :: [Type] -> Type -> Type
ravel args res = go args
  where
    go []    = res
    go (h:t) = AppT (AppT ArrowT h) (go t)

-- Construct a function type, separating the arguments with ~>
ravelDefun :: [Type] -> Type -> Type
ravelDefun args res = go args
  where
    go []    = res
    go (h:t) = AppT (AppT (ConT ''(~>)) h) (go t)

-- Apply an expression to a list of expressions using ordinary function applications.
foldAppE :: Exp -> [Exp] -> Exp
foldAppE = foldl' AppE

-- Apply an expression to a list of types using visible type applications.
foldAppTypeE :: Exp -> [Type] -> Exp
foldAppTypeE = foldl' AppTypeE

-- Apply a type to a list of types using ordinary function applications.
foldAppT :: Type -> [Type] -> Type
foldAppT = foldl' AppT

-- Apply a type to a list of types using defunctionalized applications
-- (i.e., using Apply from singletons).
foldAppDefunT :: Type -> [Type] -> Type
foldAppDefunT = foldl' (\x y -> ConT ''Apply `AppT` x `AppT` y)

-- Apply a type to a list of types using visible kind applications.
foldAppKindT :: Type -> [Type] -> Type
foldAppKindT = foldl' AppKindT

itraverse :: Applicative f => (Int -> a -> f b) -> [a] -> f [b]
itraverse f xs0 = go xs0 0 where
  go [] _ = pure []
  go (x:xs) n = (:) <$> f n x <*> (go xs $! (n + 1))

ireplicateA :: Applicative f => Int -> (Int -> f a) -> f [a]
ireplicateA cnt0 f =
    loop cnt0 0
  where
    loop cnt n
        | cnt <= 0  = pure []
        | otherwise = liftA2 (:) (f n) (loop (cnt - 1) $! (n + 1))

-----
-- Taken directly from singletons
-----

-- Make an identifier uppercase. If the identifier is infix, this acts as the
-- identity function.
upcase :: String -> String
upcase str
  | isHsLetter first
  = toUpper first : tail str

  | otherwise
  = str
  where
    first = head str

-- is it a letter or underscore?
isHsLetter :: Char -> Bool
isHsLetter c = isLetter c || c == '_'
