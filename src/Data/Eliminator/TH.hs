{-# LANGUAGE TemplateHaskell #-}
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
    -- $conventions
    deriveElim
  , deriveElimNamed
  ) where

import           Control.Applicative

import           Data.Char (isUpper)
import           Data.Foldable
import qualified Data.Kind as Kind (Type)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe
import           Data.Singletons.Prelude

import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Language.Haskell.TH.Desugar (tupleNameDegree_maybe, unboxedTupleNameDegree_maybe)

{- $conventions
TODO: snappy intro

The naming conventions are:

* If the datatype has an alphanumeric name, its eliminator will have that name
  with @elim-@ prepended.

* If the datatype has a symbolic name, its eliminator will have that name
  with @~>@ prepended.

TODO: Conventions for order of arguments

TODO: The boatloads of extensions you'll need to use this

TODO: Restrictions (can't use data families, GADTs, or polymorphic recursion,
must have Sing instance, etc.)
-}

-- | @'deriveElim' dataName@ generates a top-level elimination function for the
-- datatype @dataName@. The eliminator will follow these naming conventions:
-- The naming conventions are:
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
deriveElimNamed funName dataName = do
  info@(DatatypeInfo { datatypeVars    = vars
                     , datatypeVariant = _ -- TODO: Reject data family instances
                     , datatypeCons    = cons
                     }) <- reifyDatatype dataName
  predVar <- newName "p"
  singVar <- newName "s"
  let elimN = mkName funName
      dataVarBndrs = catMaybes $ map typeToTyVarBndr vars
      promDataKind = datatypeType info
      predVarBndr = KindedTV predVar (InfixT promDataKind ''(~>) (ConT ''Kind.Type))
      singVarBndr = KindedTV singVar promDataKind
  caseTypes <- traverse (caseType dataName predVar) cons
  let returnType  = predType predVar (VarT singVar)
      bndrsPrefix = dataVarBndrs ++ [predVarBndr]
      allBndrs    = bndrsPrefix ++ [singVarBndr]
      elimType = ForallT allBndrs []
                   (ravel (singType singVar:caseTypes) returnType)
      qelimDef
        | null cons
        = do singVal <- newName "singVal"
             pure $ FunD elimN [Clause [VarP singVal] (NormalB (CaseE (VarE singVal) [])) []]

        | otherwise
        = do caseClauses
               <- itraverse (\i -> caseClause dataName elimN
                                              (map tyVarBndrName bndrsPrefix)
                                              i (length cons)) cons
             pure $ FunD elimN caseClauses
  elimDef <- qelimDef
  pure [SigD elimN elimType, elimDef]

caseType :: Name -> Name -> ConstructorInfo -> Q Type
caseType dataName predVar
         (ConstructorInfo { constructorName   = conName
                          , constructorVars   = _ -- TODO: Reject GADTs
                          , constructorFields = fieldTypes })
  = do vars <- newNameList "f" $ length fieldTypes
       let returnType = predType predVar
                                 (foldl' AppT (ConT conName) (map VarT vars))
           mbInductiveType var varType =
             let inductiveArg = predType predVar (VarT var)
             in mbInductiveCase dataName varType inductiveArg
       pure $ foldr' (\(var, varType) t ->
                        ForallT [KindedTV var varType]
                                []
                                (ravel (singType var:maybeToList (mbInductiveType var varType)) t))
                     returnType
                     (zip vars fieldTypes)

caseClause :: Name -> Name -> [Name] -> Int -> Int
           -> ConstructorInfo -> Q Clause
caseClause dataName elimN bndrNamesPrefix conIndex numCons
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
       let singConName = singDataConName conName
           mkSingVarPat var varSig = SigP (VarP var) (singType varSig)
           singVarPats = zipWith mkSingVarPat singVars singVarSigs

           mbInductiveArg singVar singVarSig varType =
             let prefix = foldAppType (VarE elimN)
                             $ map VarT bndrNamesPrefix
                            ++ [VarT singVarSig]
                 inductiveArg = foldExp prefix
                                  $ VarE singVar:map VarE caseVars
             in mbInductiveCase dataName varType inductiveArg
           mkArg f (singVar, singVarSig, varType) =
             foldExp f $ VarE singVar
                       : maybeToList (mbInductiveArg singVar singVarSig varType)
           rhs = foldl' mkArg (VarE usedCaseVar) $
                        zip3 singVars singVarSigs fieldTypes
       pure $ Clause (ConP singConName singVarPats : map VarP caseVars)
                     (NormalB rhs)
                     []

-- TODO: Rule out polymorphic recursion
mbInductiveCase :: Name -> Type -> a -> Maybe a
mbInductiveCase dataName varType inductiveArg
  = case unfoldType varType of
      headTy :| _
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

-- | Construct a type of the form @p '@@' ty@ given @p@ and @ty@.
predType :: Name -> Type -> Type
predType p ty = InfixT (VarT p) ''(@@) ty

-- | Generate a list of fresh names with a common prefix, and numbered suffixes.
newNameList :: String -> Int -> Q [Name]
newNameList prefix n = ireplicateA n $ newName . (prefix ++) . show

eliminatorName :: Name -> String
eliminatorName n
  | first:_ <- nStr
  , isUpper first
  = "elim" ++ nStr

  | otherwise
  = "~>" ++ nStr
  where
    nStr = nameBase n

typeToTyVarBndr :: Type -> Maybe TyVarBndr
typeToTyVarBndr (SigT (VarT n) k) = Just $ KindedTV n k
typeToTyVarBndr _                 = Nothing

-- Reconstruct and arrow type from the list of types
ravel :: [Type] -> Type -> Type
ravel []    res = res
ravel (h:t) res = AppT (AppT ArrowT h) (ravel t res)

-- apply an expression to a list of expressions
foldExp :: Exp -> [Exp] -> Exp
foldExp = foldl' AppE

-- apply an expression to a list of types
foldAppType :: Exp -> [Type] -> Exp
foldAppType = foldl' AppTypeE

-- | Decompose an applied type into its individual components. For example, this:
--
-- @
-- Either Int Char
-- @
--
-- would be unfolded to this:
--
-- @
-- Either :| [Int, Char]
-- @
unfoldType :: Type -> NonEmpty Type
unfoldType = go []
  where
    go :: [Type] -> Type -> NonEmpty Type
    go acc (AppT t1 t2)    = go (t2:acc) t1
    go acc (SigT t _)      = go acc t
    go acc (ForallT _ _ t) = go acc t
    go acc t               = t :| acc

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV  n)   = n
tyVarBndrName (KindedTV n _) = n

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

singDataConName :: Name -> Name
singDataConName nm
  | nm == '[]                                      = 'SNil
  | nm == '(:)                                     = 'SCons
  | Just degree <- tupleNameDegree_maybe nm        = mkTupleDataName degree
  | Just degree <- unboxedTupleNameDegree_maybe nm = mkTupleDataName degree
  | otherwise                                      = prefixUCName "S" ":%" nm

mkTupleDataName :: Int -> Name
mkTupleDataName n = mkName $ "STuple" ++ (show n)

-- put an uppercase prefix on a name. Takes two prefixes: one for identifiers
-- and one for symbols
prefixUCName :: String -> String -> Name -> Name
prefixUCName pre tyPre n = case (nameBase n) of
    (':' : rest) -> mkName (tyPre ++ rest)
    alpha -> mkName (pre ++ alpha)
