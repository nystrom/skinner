{-# LANGUAGE FlexibleInstances #-}

module Main (main) where

import           Control.Applicative  ((*>), (<$), (<$>), (<*), (<*>))
import Control.Applicative ((<|>))
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Char            (isLower, isUpper, toLower, toUpper)
import           Data.List            (find, intercalate, intersect, minimum,
                                       minimumBy, nub, sortBy, sortOn, (\\))
import qualified Data.Map             as M
import           Data.Maybe           (catMaybes, fromMaybe, fromJust, isJust, isNothing,
                                       listToMaybe, mapMaybe)
import           Data.Monoid
import           Data.Tuple           (swap)

import           Debug.Trace          (trace)

import           System.Environment   (getArgs)

import           Text.Parsec          (parse)
import           Text.Parsec.String

import           Aliases
import           AST
import           JASTParse
import           SkinParse
import           Typer

type Cost = Double

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

freeVars :: JExp -> [(String, Type)]
freeVars (JNew es t)   = nub $ concatMap freeVars es
freeVars (JOp op es t) = nub $ concatMap freeVars es
freeVars (JK k t)      = []
freeVars (JVar x t)    = [(x, t)]

instance Wordy JExp where
  toBagOfWords (JNew es t)   = toBagOfWords t ++ concatMap toBagOfWords es
  toBagOfWords (JOp op es t) = [] -- toBagOfWords t
  toBagOfWords (JK k t)      = k' : [] -- toBagOfWords t
        where 
          k' = case dropWhile (/='.') k of
                "" -> k
                k -> dropWhile (=='.') k
  toBagOfWords (JVar x t)    = [] -- toBagOfWords t    -- NOTE: do not include the variable name

instance Wordy Type where
  toBagOfWords (TCon label []) = [label]
  toBagOfWords _               = []

isNullable :: Type -> Bool
isNullable = not . isPrimitive

isPrimitiveNumber :: Type -> Bool
isPrimitiveNumber (TCon "byte" [])   = True
isPrimitiveNumber (TCon "short" [])  = True
isPrimitiveNumber (TCon "char" [])   = True
isPrimitiveNumber (TCon "int" [])    = True
isPrimitiveNumber (TCon "long" [])   = True
isPrimitiveNumber (TCon "float" [])  = True
isPrimitiveNumber (TCon "double" []) = True
isPrimitiveNumber t                  = False

isPrimitive :: Type -> Bool
isPrimitive (TCon "void" [])    = True
isPrimitive (TCon "boolean" []) = True
isPrimitive t                   = isPrimitiveNumber t

isBuiltin :: Type -> Bool
isBuiltin (TCon "void" [])                = True
isBuiltin (TCon "Object" [])              = True
isBuiltin (TCon "String" [])              = True
isBuiltin (TCon "java.lang.Object" [])    = True
isBuiltin (TCon "java.lang.String" [])    = True
isBuiltin (TCon "java.lang.Byte" [])      = True
isBuiltin (TCon "java.lang.Short" [])     = True
isBuiltin (TCon "java.lang.Character" []) = True
isBuiltin (TCon "java.lang.Integer" [])   = True
isBuiltin (TCon "java.lang.Long" [])      = True
isBuiltin (TCon "java.lang.Float" [])     = True
isBuiltin (TCon "java.lang.Double" [])    = True
isBuiltin (TCon "java.lang.Boolean" [])   = True
isBuiltin (TCon "java.lang.Void" [])      = True
isBuiltin (TCon "Maybe" [t])              = isBuiltin t
isBuiltin (TCon "Array" [t])              = isBuiltin t
isBuiltin (TCon "List" [t])               = isBuiltin t
isBuiltin (TCon "(,)" [t1,t2])            = isBuiltin t1 && isBuiltin t2
isBuiltin (TCon "(,,)" [t1,t2,t3])        = isBuiltin t1 && isBuiltin t2 && isBuiltin t3
isBuiltin t                               = isPrimitive t

boxedType :: Type -> Maybe Type
boxedType (TCon "byte" [])    = Just $ TCon "java.lang.Byte" []
boxedType (TCon "short" [])   = Just $ TCon "java.lang.Short" []
boxedType (TCon "char" [])    = Just $ TCon "java.lang.Character" []
boxedType (TCon "int" [])     = Just $ TCon "java.lang.Integer" []
boxedType (TCon "long" [])    = Just $ TCon "java.lang.Long" []
boxedType (TCon "float" [])   = Just $ TCon "java.lang.Float" []
boxedType (TCon "double" [])  = Just $ TCon "java.lang.Double" []
boxedType (TCon "boolean" []) = Just $ TCon "java.lang.Boolean" []
boxedType (TCon "void" [])    = Just $ TCon "java.lang.Void" []
boxedType _                   = Nothing

convertPrimitive :: Type -> Type -> JExp -> Maybe JExp
convertPrimitive (TCon s []) (TCon t []) e | s == t = Just e
convertPrimitive (TCon s []) (TCon t []) e | isPrimitiveNumber (TCon s []) && isPrimitiveNumber (TCon t []) = Just $ JOp (s ++ "2" ++ t) [e] (TCon t [])
convertPrimitive _ _ _ = Nothing

isBuiltinOp :: JExp -> Bool
isBuiltinOp (JOp "Just" [e] t) =  True
isBuiltinOp (JK "()" t) = True
isBuiltinOp (JK "Nothing" t) = True
isBuiltinOp (JK "Nil" (TCon _ [base])) = True
isBuiltinOp (JOp ":" es t) = True
isBuiltinOp (JOp "++" es t) = True
isBuiltinOp (JOp "toMaybe" [e] (TCon _ [base])) = True
isBuiltinOp (JOp "unMaybe" [e] (TCon _ [base])) = True
isBuiltinOp (JOp "maybeToList" [e] (TCon _ [base])) = True
isBuiltinOp (JOp "listToArray" [e] (TCon _ [base])) = True
isBuiltinOp (JOp "arrayToList" [e] (TCon _ [base])) = True
isBuiltinOp (JOp "toArray2" [e1, e2] (TCon _ [base])) = True
isBuiltinOp (JOp "toList2" [e1, e2] (TCon _ [base])) = True
isBuiltinOp (JOp "long2int" [e] t) = True
isBuiltinOp (JOp "float2int" [e] t) = True
isBuiltinOp (JOp "double2int" [e] t) = True
isBuiltinOp (JOp "int2float" [e] t) = True
isBuiltinOp (JOp "long2float" [e] t) = True
isBuiltinOp (JOp "double2float" [e] t) = True
isBuiltinOp (JOp "int2long" [e] t) = True
isBuiltinOp (JOp "float2long" [e] t) = True
isBuiltinOp (JOp "double2long" [e] t) = True
isBuiltinOp (JOp "float2double" [e] t) = True
isBuiltinOp (JOp "int2double" [e] t) = True
isBuiltinOp (JOp "long2double" [e] t) = True
isBuiltinOp (JOp "unbox_int" [e] t) = True
isBuiltinOp (JOp "unbox_long" [e] t) = True
isBuiltinOp (JOp "unbox_float" [e] t) = True
isBuiltinOp (JOp "unbox_double" [e] t) = True
isBuiltinOp (JOp "box_int" [e] t) = True
isBuiltinOp (JOp "box_long" [e] t) = True
isBuiltinOp (JOp "box_float" [e] t) = True
isBuiltinOp (JOp "box_double" [e] t) = True
isBuiltinOp (JOp "charToString" [e] t) = True
isBuiltinOp (JOp "stringToChar" [e] t) = True
isBuiltinOp (JOp "size" [e] t) = True
isBuiltinOp (JOp "isEmpty" [e] t) = True
isBuiltinOp (JOp "length" [e] t) = True
isBuiltinOp e = False

coerce :: SubtypeEnv -> JExp -> Type -> Maybe JExp
coerce hierarchy e t = go (typeof e) t
  where
    -- s <: t
    go s t | s == t = Just e
    go s t | isSubtype hierarchy s t = Just e

    -- don't generate coercions to or from List[List[t]], etc.
    go (TCon "List" [TCon "List" _]) _ = Nothing
    go (TCon "List" [TCon "Array" _]) _ = Nothing
    go (TCon "List" [TCon "Maybe" _]) _ = Nothing
    go (TCon "Array" [TCon "List" _]) _ = Nothing
    go (TCon "Array" [TCon "Array" _]) _ = Nothing
    go (TCon "Array" [TCon "Maybe" _]) _ = Nothing
    go (TCon "Maybe" [TCon "List" _]) _ = Nothing
    go (TCon "Maybe" [TCon "Array" _]) _ = Nothing
    go (TCon "Maybe" [TCon "Maybe" _]) _ = Nothing
    go _ (TCon "List" [TCon "List" _]) = Nothing
    go _ (TCon "List" [TCon "Array" _]) = Nothing
    go _ (TCon "List" [TCon "Maybe" _]) = Nothing
    go _ (TCon "Array" [TCon "List" _]) = Nothing
    go _ (TCon "Array" [TCon "Array" _]) = Nothing
    go _ (TCon "Array" [TCon "Maybe" _]) = Nothing
    go _ (TCon "Maybe" [TCon "List" _]) = Nothing
    go _ (TCon "Maybe" [TCon "Array" _]) = Nothing
    go _ (TCon "Maybe" [TCon "Maybe" _]) = Nothing

    -- int -> long, etc
    go s t | isPrimitiveNumber s && isPrimitiveNumber t = convertPrimitive s t e

    go s t | boxedType s == Just t = Just $ JOp ("box_" ++ label s) [e] t
      where label (TCon l _) = l
    go s t | boxedType t == Just s = Just $ JOp ("unbox_" ++ label s) [e] t
      where label (TCon l _) = l

    go (TCon "char" []) (TCon "String" []) = Just $ JOp "charToString" [e] t
    go (TCon "String" []) (TCon "char" []) = Just $ JOp "stringToChar" [e] t
    go (TCon "String" []) (TCon "Array" [TCon "char" []]) = Just $ JOp "stringToCharArray" [e] t

    -- List[void] --> int
    -- Array[void] --> int
    -- Maybe[void] --> boolean
    go (TCon "List" [TCon "void" []]) (TCon "int" []) = Just $ JOp "size" [e] t
    go (TCon "Array" [TCon "void" []]) (TCon "int" []) = Just $ JOp "length" [e] t
    go (TCon "Maybe" [TCon "void" []]) (TCon "boolean" []) = Just $ JOp "isEmpty" [e] t

    -- Maybe[int] --> Integer
    go (TCon "Maybe" [TCon "byte" []]) (TCon "java.lang.Byte" []) = Just $ JOp "boxMaybeByte" [e] t
    go (TCon "Maybe" [TCon "short" []]) (TCon "java.lang.Short" []) = Just $ JOp "boxMaybeShort" [e] t
    go (TCon "Maybe" [TCon "char" []]) (TCon "java.lang.Character" []) = Just $ JOp "boxMaybeChar" [e] t
    go (TCon "Maybe" [TCon "int" []]) (TCon "java.lang.Integer" []) = Just $ JOp "boxMaybeInt" [e] t
    go (TCon "Maybe" [TCon "long" []]) (TCon "java.lang.Long" []) = Just $ JOp "boxMaybeLong" [e] t
    go (TCon "Maybe" [TCon "float" []]) (TCon "java.lang.Float" []) = Just $ JOp "boxMaybeFloat" [e] t
    go (TCon "Maybe" [TCon "double" []]) (TCon "java.lang.Double" []) = Just $ JOp "boxMaybeDouble" [e] t
    go (TCon "Maybe" [TCon "boolean" []]) (TCon "java.lang.Boolean" []) = Just $ JOp "boxMaybeBoolean" [e] t


    -- TODO: lookup the actual field name!

    -- (t,void) -> t
    go (TCon label [u, TCon "void" []]) t | u == t = Just $ JOp (label ++ ".1") [e] t
    -- (void,t) -> t
    go (TCon label [TCon "void" [], u]) t | u == t = Just $ JOp (label ++ ".2") [e] t
    -- (u,v,void) -> (u,v)
    go (TCon label [u, v, TCon "void" []]) (TCon label2 [u', v']) | u == u' && v == v' = Just $ JOp label2 [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (u,void,v) -> (u,v)
    go (TCon label [u, TCon "void" [], v]) (TCon label2 [u', v']) | u == u' && v == v' = Just $ JOp label2 [JOp (label ++ ".1") [e] u, JOp (label ++ ".3") [e] v] t
    -- (void,u,v) -> (u,v)
    go (TCon label [TCon "void" [], u, v]) (TCon label2 [u', v']) | u == u' && v == v' = Just $ JOp label2 [JOp (label ++ ".2") [e] u, JOp (label ++ ".3") [e] v] t
    -- (u,void,void) -> (u)
    go (TCon label [u, TCon "void" [], TCon "void" []]) (TCon label2 [u']) | u == u' = Just $ JOp label2 [JOp (label ++ ".1") [e] u] t
    -- (void,u,void) -> (u)
    go (TCon label [TCon "void" [], u, TCon "void" []]) (TCon label2 [u']) | u == u' = Just $ JOp label2 [JOp (label ++ ".2") [e] u] t
    -- (void,void,u) -> (u)
    go (TCon label [TCon "void" [], TCon "void" [], u]) (TCon label2 [u']) | u == u' = Just $ JOp label2 [JOp (label ++ ".3") [e] u] t
    -- (u,void,void) -> (u)
    go (TCon label [u, TCon "void" [], TCon "void" []]) t | u == t = Just $ JOp (label ++ ".1") [e] t
    -- (void,u,void) -> (u)
    go (TCon label [TCon "void" [], u, TCon "void" []]) t | u == t = Just $ JOp (label ++ ".2") [e] t
    -- (void,void,u) -> (u)
    go (TCon label [TCon "void" [], TCon "void" [], u]) t | u == t = Just $ JOp (label ++ ".3") [e] t

    -- HACK: we should allow these, but with lower cost that converting two expressions to a list.
    -- This ensures Add matches Plus better than UnaryPlus.
    -- Or have negative aliases: Add !~ UnaryPlus, Method !~ Lambda, etc.

    -- t -> List[t]
    -- go s (TCon "List" [w]) | s == w = Just $ JOp "toList1" [e] t
    -- t -> Array[t]
    -- go s (TCon "Array" [w]) | s == w = Just $ JOp "toArray1" [e] t
    -- t -> Maybe[t]
    go s (TCon "Maybe" [w]) | s == w = Just $ JOp "toMaybe" [e] t
    -- List[t] -> Array[t]
    go (TCon "List" [u]) (TCon "Array" [w]) | u == w = Just $ JOp "listToArray" [e] t
    -- Array[t] -> List[t]
    go (TCon "Array" [u]) (TCon "List" [w]) | u == w = Just $ JOp "arrayToList" [e] t
    -- Maybe[t] -> List[t]
    go (TCon "Maybe" [u]) (TCon "List" [w]) | u == w = Just $ JOp "maybeToList" [e] t
    -- List[t] -> Maybe[t]
    go (TCon "List" [u]) (TCon "Maybe" [w]) | u == w = Just $ JOp "listToMaybe" [e] t
    -- Maybe[t] -> t
    go (TCon "Maybe" [u]) t | u == t && isNullable t = Just $ JOp "unMaybe" [e] t

    -- (t,t) -> [t]
    go (TCon label [u, v]) (TCon "List" [w]) | u == w && v == w = Just $ JOp "toList2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t,t) -> [t]
    go (TCon label [u, v, w]) (TCon "List" [x]) | u == x && v == x && w == x = Just $ JOp "toList2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t) -> [t]
    go (TCon label [u, v]) (TCon "Array" [w]) | u == w && v == w = Just $ JOp "toArray2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t,t) -> [t]
    go (TCon label [u, v, w]) (TCon "Array" [x]) | u == x && v == x && w == x = Just $ JOp "toArray2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (s,t) -> s
    go (TCon label [u, v]) t | u == t = Just $ JOp (label ++ ".1") [e] t
    -- (s,t) -> t
    go (TCon label [u, v]) t | v == t = Just $ JOp (label ++ ".2") [e] t
    -- (s,t,u) -> s
    go (TCon label [u, v, w]) t | u == t = Just $ JOp (label ++ ".1") [e] t
    -- (s,t,u) -> s
    go (TCon label [u, v, w]) t | v == t = Just $ JOp (label ++ ".2") [e] t
    -- (s,t,u) -> s
    go (TCon label [u, v, w]) t | w == t = Just $ JOp (label ++ ".3") [e] t

    -- K t -> t
    go (TCon label [u]) t | u == t = Just $ JOp (label ++ ".1") [e] t

    -- K u -> K t -> t
    go (TCon label [u]) t = case coerce hierarchy e (TCon label [t]) of
                                Just e  -> coerce hierarchy e t
                                Nothing -> Nothing
{-
    -- s -> K s -> K t
    go s (TCon label [w]) = case coerce hierarchy e (TCon label [s]) of
                              Just e -> coerce hierarchy e (TCon label [w])
                              Nothing -> Nothing
-}

    -- no coercion
    go s t = Nothing

substVars :: [(String, JExp)] -> JExp -> JExp
substVars s (JNew es t)  = JNew (map (substVars s) es) t
substVars s (JOp k es t) = JOp k (map (substVars s) es) t
substVars s (JK k t)     = JK k t
substVars s (JVar x t)   = fromMaybe (JVar x t) (lookup x s)

-- Find the free variables of the expression.
-- Find a factory method with matching arguments and matching name.
matchConstructors :: JExp -> Reader (Skin, SubtypeEnv) MatchResult
matchConstructors (new @ (JNew args typ @ (TCon label []))) = do
  (skin, hierarchy) <- trace ("match constructors vs " ++ show new) ask

  let fv = freeVars new

  rs <- forM (factories skin) $ \k @ (JConstructor skinLabel skinFields skinSuper) -> do -- trace ("matching " ++ show k ++ " vs " ++ show new) $ do

    -- make a substitution that coerces the factory method parameters (skinFields) to the right type for the
    -- free variables (fv) of the constructor call.

    theta <- do -- trace ("matching " ++ show skinFields ++ " in " ++ show k ++ " with " ++ show fv) $ do
      case (skinFields, fv) of
        -- HACK: if there are more parameter to the factory method than there are free variables in
        -- the constructor call, try to group the parameters into a list or array.
        -- For now, just handle two parameters. This handles the case of binary operators
        -- that are implemented using lists of operands in the Java AST.
        ([(y1, t1'), (y2, t2')], [(x, TCon "List" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "toList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) (TCon "List" [t]) of
            Just e  -> return [(x, e, True)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, TCon "Array" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "toArray2" [JVar y1 t1', JVar y2 t1'] (TCon "Array" [t1'])) (TCon "Array" [t]) of
            Just e  -> return [(x, e, True)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, t)]) | t1' == t2' ->
          case coerce hierarchy (JOp "toList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) t of
            Just e  -> return [(x, e, True)]
            Nothing -> return []

        (skinFields, fv) | length skinFields == length fv -> do

          -- We have a call to a constructor in the Java AST.
          -- We want to see if we can invoke that constructor from the given factory method in the Skin.

          -- To do this, we see if we can coerce each of the parameters of the factory method
          -- into an argument of the constructor call.

          -- We need to cover all arguments to the constructor call (i.e., those that are free variables of the `new` JExp).

          -- We just assume the free variables and factory parameters are in the same order. This could be relaxed when the types are different.
          -- In particular, we might have a separate enum parameter that (e.g., PLUS on a BinaryExpression node) that could go anywhere in the parameter list.

          -- TODO: we need to handle extra arguments like a Position.

          otheta <- forM (zip fv skinFields) $ \((x, t), (y, t')) ->
            case coerce hierarchy (JVar y t') t of
              Just e  -> return $ Just (x, e, e /= (JVar y t'))
              Nothing -> return Nothing

          let theta = catMaybes otheta

          return theta
        _ ->
          return []

    if length theta == length fv
      then do
        let cost = minimum $ map (matchName skin skinLabel) (toBagOfWords new)
        let numCoerced = length $ filter (\(_,_,coerced) -> coerced) theta
        let coercionCost = if null fv then 0 else fromIntegral numCoerced / fromIntegral (length fv)
        return [(cost + coercionCost, k, substVars (map (\(x,e,coerced) -> (x,e)) theta) new)]
      else
        return []

  case sortOn (\(a,b,c) -> a) (concat rs) of
    ((a,b,c):rs) -> return $ Match a b c
    _            -> return $ NoMatch new

matchConstructors e = return $ NoMatch e

type SubtypeEnv = M.Map String Type

supertype :: SubtypeEnv -> Type -> Maybe Type
supertype env TBoh = Nothing
supertype env (TCon "Object" []) = Nothing
supertype env (TVar x)           = Just $ TCon "Object" []
supertype env (TCon label [])    = M.lookup label env

-- lists, arrays, and maybe are covariant
supertype env (TCon "List" [TCon "Object" []])  = Just $ TCon "Object" []
supertype env (TCon "List" [t])  = (TCon "List" . return) <$> supertype env t
supertype env (TCon "Array" [TCon "Object" []])  = Just $ TCon "Object" []
supertype env (TCon "Array" [t])  = (TCon "Array" . return) <$> supertype env t
supertype env (TCon "Maybe" [TCon "Object" []])  = Just $ TCon "Object" []
supertype env (TCon "Maybe" [t])  = (TCon "Maybe" . return) <$> supertype env t

-- primitive types have no direct supertype
supertype env t | isPrimitive t  = Nothing
-- other types are subtype of Object
supertype env t  = Just $ TCon "Object" []

isSubtype :: SubtypeEnv -> Type -> Type -> Bool
isSubtype env t1 (TCon "Object" []) = True
isSubtype env t1 t2 | t1 == t2 = True
isSubtype env t1 t2 = case supertype env t1 of
                   Nothing -> False
                   Just t  -> isSubtype env t t2

matchName :: Skin -> String -> String -> Double
matchName skin = matchNameWithAliases (aliases skin)

-- match interface types in the skin to the JAST, rewriting the skin
matchTypes :: Monad m => Skin -> JAST -> m Skin
matchTypes skin jast = do
  let subst = matchInterfaces skin jast
  return $ trace ("subst " ++ show subst) $ substSkin subst skin

-- Is the skin type used for this particular substitution
typeUsed :: Subst -> Type -> Bool
typeUsed s t                  | isBuiltin t = True
typeUsed s (TCon "Array" [t])  = typeUsed s t
typeUsed s (TCon "List" [t])  = typeUsed s t
typeUsed s (TCon "Maybe" [t]) = typeUsed s t
typeUsed s (TCon "(,)" [t1,t2]) = typeUsed s t1 && typeUsed s t2
typeUsed s (TCon "(,,)" [t1,t2,t3]) = typeUsed s t1 && typeUsed s t2 && typeUsed s t3
typeUsed s (TCon label [])    = isJust (lookup (Tyvar label) s)
typeUsed s t                  = False

-- Is the skin type used for this substitution and does it map to a Java class.
classUsed :: Subst -> Type -> Bool
classUsed s (TCon "Object" []) = True
classUsed s t                  | isBuiltin t = False
classUsed s (TCon label [])    = case lookup (Tyvar label) s of
                                   Just (TCon t []) -> True
                                   _ -> False
classUsed s t                  = False

-- Apply the type substitution to the skin.
substSkin :: Subst -> Skin -> Skin
substSkin s skin = skin { interfaces = mapMaybe (fmap substInterface . fixInterface) (interfaces skin),
                          factories = mapMaybe (fmap substFactory . fixFactory) (factories skin),
                          rules = mapMaybe (fmap substRule . fixRule) (rules skin),
                          tokens = mapMaybe (fmap substToken . fixToken) (tokens skin),
                          templates = mapMaybe (fmap substTemplate . fixTemplate) (templates skin) }
  where
    fixToken :: (String, Type) -> Maybe (String, Type)
    fixToken (x, t) | typeUsed s t = Just (x, t)
    fixToken _      = Nothing

    fixInterface :: JInterface -> Maybe JInterface
    fixInterface (JInterface label t) = do
      guard $ classUsed s (TCon label [])
      guard $ classUsed s t
      return $ JInterface label t

    fixRule :: Rule -> Maybe Rule
    fixRule (Rule t lhs rhs e) = do
      rhs' <- fixRhs rhs
      e' <- fixExp e <|> return (JK "null" (typeof e))
      guard $ typeUsed s t
      return $ Rule t lhs rhs' e'

    fixTemplate :: Template -> Maybe Template
    fixTemplate (Template t1 t2 rhs e) = do
      rhs' <- fixRhs rhs
      e' <- fixExp e
      guard $ typeUsed s t1
      guard $ typeUsed s t2
      return $ Template t1 t2 rhs' e'

    toTyvar t | isBuiltin t = t
    toTyvar t @ (TCon label []) | isBuiltin t = TVar (Tyvar label)
    toTyvar (TCon label ts) = TCon label (map toTyvar ts)

    fixExp :: JExp -> Maybe JExp
    fixExp (JVar x t)   | typeUsed s t = Just $ JVar x t
    fixExp (JNew es t)  = Just $ JNew (mapMaybe fixExp es) t

    -- use mapM to return Nothing if any sub-exp cannot be fixed
    -- use mapMaybe to return Nothing if all sub-exps cannot be fixed -- this will remove unfixed expressions

    -- allow the built-in operations
    fixExp e @ (JOp op es t) | isBuiltinOp e = do
      es' <- mapM fixExp es
      return $ JOp op es' t

    fixExp (JOp k es t) | trace ("fixExp " ++ show (JOp k es t) ++ " -- subst type " ++ show (substType t)) False = undefined

    fixExp (JOp k es t) | typeUsed s t && not (isBuiltin (substType t)) = do
      -- EXCLUDE builtin types here since we need to eliminate the constructor call for these
      let es' = mapMaybe fixExp es
      return $ JOp k es' t


    fixExp (JOp k es t) | trace ("fixExp not used or built-in " ++ show (JOp k es t) ++ " -- " ++ show s) False = undefined
    fixExp (JOp k es t) | typeUsed s t = do
      let es' = mapMaybe fixExp es
      -- eliminate calls to factory methods
      -- the logic is duplicated here from fixPrimitiveMatch ... should be merged
      let subclasses = filter (\(JConstructor k' args super) -> super == t && k == k') (factories skin)
      case subclasses of
        [JConstructor k [] _] ->
          Just $ JK "()" (TCon "void" [])
        [JConstructor k [(x, t)] _] -> do
          -- replace the constructor call with just the argument
          es'' <- mapM fixExp es
          case es'' of
            [e] -> Just e
            _ -> error $ "bad constructor match " ++ k
        [JConstructor k xts _] -> do
          let ts = map typeof es
          let tt = tupleType ts
          let (TCon label _) = tt
          Just $ JOp label es' tt
        _ -> {- leave it alone -}
          Just $ JOp k es' t
    fixExp (JK k t)     | typeUsed s t = Just $ JK k t
    fixExp e            = Nothing

    fixRhs :: [(Sym, String)] -> Maybe [(Sym, String)]
    fixRhs [] = Just []
    fixRhs rhs = case (mapMaybe fixElement rhs) of   -- if we make a non-empty RHS empty, remove it
      [] -> Nothing
      rhs' -> Just rhs'

    fixElement :: (Sym, String) -> Maybe (Sym, String)
    fixElement (Nonterminal a, x) | nonterminalUsed a = Just (Nonterminal a, x)
    fixElement (Terminal a, x)    | tokenUsed a       = Just (Terminal a, x)
    fixElement (Literal a, x)                         = Just (Literal a, x)
    fixElement _ = Nothing

    tokenUsed :: String -> Bool
    tokenUsed a = case find ((== a) . fst) (tokens skin) of
                    Just (x, t) -> typeUsed s t
                    Nothing     -> False

    nonterminalUsed :: String -> Bool
    nonterminalUsed a = case find (\(Rule t lhs _ _) -> lhs == a) (rules skin) of
                          Just (Rule t _ _ _) -> typeUsed s t
                          Nothing             -> False

    fixFields :: [(String, Type)] -> [(String, Type)]
    fixFields = filter (typeUsed s . snd)

    fixFactory :: JConstructor -> Maybe JConstructor
    fixFactory (JConstructor label fields t) = do
      guard $ classUsed s t
      return $ JConstructor label (fixFields fields) t

    substTemplate (Template t1 t2 rhs e) = Template (substType t1) (substType t2) rhs (substExp e)

    substToken (x, t) = (x, substType t)

    substInterface (JInterface label super) = JInterface (substLabel label) (substType super)

    substFactory (JConstructor label fields super) = JConstructor label (map substField fields) (substType super)

    substRule (Rule typ label rhs e) = Rule (substType typ) label rhs (substExp e)

    substField (x,t) = (x, substType t)

    -- Constructors in the skin are treated as type variables.
    substType t | isBuiltin t = t
    substType (TCon label []) = substType (TVar (Tyvar label))
    substType (TCon k ts) = TCon k (map substType ts)
    substType t               = substTy s t

    substLabel l = case substType (TCon l []) of
      TCon x []      -> x
      TVar (Tyvar x) -> x
      _              -> error $ "cannot substitute label " ++ l

    substExp e = do
      let e' = substExp' e
      case typeof e' of
        TCon "void" [] -> JK "()" (TCon "void" [])
        t              -> e'

    substExp' (JNew es t)  = JNew (map substExp es) (substType t)
    -- substExp' (JNew es t) = JNew (map (substExp s) es) t -- do not substitute classes
    substExp' (JOp k es t) = JOp k (map substExp es) (substType t)
    substExp' (JK k t)     = JK k (substType t)
    substExp' (JVar x t)   = JVar x (substType t)

-- Remove all unused factories.
-- Remove any rule that calls a dead factory.
-- Remove any dead nonterminals from RHSs. If this causes a rule to become an epsilon rule, remove the rule.
-- Repeat...

fixRules :: ([Rule] -> [Rule]) -> [Rule] -> [Rule]
-- fixRules f rules | trace ("fix " ++ show rules) False = undefined
fixRules f rules = do
  let rules' = f rules
  if rules == rules'
    then rules
    else fixRules f rules'

removeUnusedRules :: [MatchResult] -> [Rule] -> [Rule]
removeUnusedRules matchResults = (fixRules (reachableRules . removeRulesWithUndefinedRHS . removeDeadRules)) . coveredRules
  where
    coveredRules = findCoveredRules (mapMaybe getConstructor matchResults)

    reachableRules rules = reachable rules (startRules rules)

    startRules rules = case goal rules of
      Nothing -> []
      Just s -> findRulesFor s rules

    -- HACK -- hardcode the start rule as goal
    goal _ = Just "goal"
    -- goal (Rule _ x _ _:rs) = Just x
    -- goal [] = Nothing

    tracef s f x = trace (s ++ "(" ++ show x ++  ") = " ++ show (f x)) (f x)

    -- filter all rules where the LHS is used in some other rule
    removeDeadRules :: [Rule] -> [Rule]
    removeDeadRules rules | trace ("removeDeadRules " ++ show rules) False = undefined
    removeDeadRules rules = filter ruleUsed rules
      where
        ruleUsed = tracef "ruleUsed" ruleUsed2
        ruleUsed2 (Rule _ lhs _ _) = lhs == "goal" || any (ntUsed lhs) rules

        ntUsed lhs (Rule _ _ rhs _) = any (ntUsed' lhs) rhs

        ntUsed' lhs (Nonterminal x, _) = x == lhs
        ntUsed' lhs _ = False

    -- filter all rules where all nonterminals on the RHS are defined
    removeRulesWithUndefinedRHS :: [Rule] -> [Rule]
    removeRulesWithUndefinedRHS rules | trace ("removeRulesWithUndefinedRHS " ++ show rules) False = undefined
    removeRulesWithUndefinedRHS rules = filter ruleDefined rules
      where
        ruleDefined = tracef "ruleDefined" ruleDefined2
        ruleDefined2 (Rule _ lhs [] _) = True
        ruleDefined2 (Rule _ lhs rhs _) = all rhsDefined rhs

        rhsDefined (Nonterminal x, _) = x `elem` map (\(Rule _ lhs _ _) -> lhs) rules
        rhsDefined (Terminal x, _) = True
        rhsDefined (Literal x, _) = True

    findRulesFor :: String -> [Rule] -> [Rule]
    findRulesFor lhs = filter (\(Rule _ x _ _) -> lhs == x)

    reachable :: [Rule] -> [Rule] -> [Rule]
    reachable allRules rules = (fixRules (\rules -> nub (moreRules rules))) rules
      where
        moreRules :: [Rule] -> [Rule]
        moreRules rules = concatMap (`findRulesFor` allRules) (nonterminals rules)

        nonterminals :: [Rule] -> [String]
        nonterminals rules = nub $ concatMap nonterminalsInRule rules

        nonterminalsInRule :: Rule -> [String]
        nonterminalsInRule (Rule t lhs rhs e) = nub $ lhs : mapMaybe nt rhs

        nt (Nonterminal x, _) = Just x
        nt _ = Nothing

    getConstructor :: MatchResult -> Maybe JConstructor
    getConstructor (Match cost c e) = Just c
    getConstructor _ = Nothing

-- find all the covered rules
-- these are rules that either invoke a matched constructor or invoke no constructor
findCoveredRules :: [JConstructor] -> [Rule] -> [Rule]
findCoveredRules ks = filter ruleInvokesOnlyTheseConstructors
  where
    ruleInvokesOnlyTheseConstructors (Rule t lhs rhs e) = expInvokesOnlyTheseConstructors e

    expInvokesOnlyTheseConstructors (JVar x t)    = True
    expInvokesOnlyTheseConstructors (JK k t)      = True
    expInvokesOnlyTheseConstructors (JNew es t)   = all expInvokesOnlyTheseConstructors es
    expInvokesOnlyTheseConstructors e @ (JOp op es t) | isBuiltinOp e = all expInvokesOnlyTheseConstructors es
    expInvokesOnlyTheseConstructors (JOp op es t) = any (\(JConstructor label _ _) -> label == op) ks && all expInvokesOnlyTheseConstructors es

    typeMatchesTheseConstructors t | trace ("typeMatchesTheseConstructors " ++ show t) False = undefined
    typeMatchesTheseConstructors t | isBuiltin t = True
    typeMatchesTheseConstructors (TCon "List" [t]) = typeMatchesTheseConstructors t
    typeMatchesTheseConstructors (TCon "Maybe" [t]) = typeMatchesTheseConstructors t
    typeMatchesTheseConstructors (TCon "Array" [t]) = typeMatchesTheseConstructors t
    typeMatchesTheseConstructors (TCon "(,)" ts) = all typeMatchesTheseConstructors ts
    typeMatchesTheseConstructors (TCon "(,,)" ts) = all typeMatchesTheseConstructors ts
    typeMatchesTheseConstructors (TCon label []) = any (\(JConstructor label' _ _) -> label == label') ks

data MatchResult = Match Cost JConstructor JExp
                 | NoMatch JExp
  deriving Show

isMatch (Match _ _ _) = True
isMatch _ = False

class ConvertToType a where
  toType :: a -> Type

instance ConvertToType JInterface where
  toType (JInterface label _) = TCon label []

instance ConvertToType JConstructor where
  toType (JConstructor label _ _) = TCon label []

toTypeVar (JInterface label _) = Tyvar label

swizzle :: Show a => [[a]] -> [[a]]
swizzle []          = []
swizzle [ys]        = map return ys
swizzle ([]:ys)     = swizzle ys
swizzle ((x:xs):ys) = map (\s -> x:s) (swizzle ys) ++ swizzle (xs:ys)

-- match types (not classes)
--   use subtypes as weights...
--   should end up mapping stm AND exp to exp
matchInterfaces :: Skin -> JAST -> Subst
matchInterfaces skin jast = result
  where
    is :: [Tyvar]
    is = map toTypeVar (interfaces skin)

    js :: [Type]
    js = map toType (jinterfaces jast)

    ihierarchy :: SubtypeEnv
    ihierarchy = makeHierarchy (interfaces skin) (factories skin)

    jhierarchy :: SubtypeEnv
    jhierarchy = makeHierarchy (jinterfaces jast) (jconstructors jast)

    result :: Subst
    result = s1 ++ s2
      where
        s1 = findSubst
        missing = filter (not . (`elem` map fst s1)) is
        s2 = mapMaybe (findPrimitiveMatch s1) missing
        -- TODO: we only use the original s1 in the substitions in findPrimitiveMatch, but we should recursively use s2
        -- But naively doing so creates a <loop>

    -- If there is just one factory for the given type and one field, match that type.
    -- If there are no factories, match with void.
    -- Otherwise, no match!
    findPrimitiveMatch :: Subst -> Tyvar -> Maybe (Tyvar, Type)
    -- findPrimitiveMatch (Tyvar "IDENTIFIER") = Just (Tyvar "IDENTIFIER", TCon "String" [])
    findPrimitiveMatch subst (Tyvar i) = do
        let subclasses = filter (\(JConstructor k args (TCon super _)) -> super == i) (factories skin)
        case subclasses of
          [] -> Just (Tyvar i, TCon "void" [])
          [JConstructor k [] _] ->
            return (Tyvar i, TCon "void" [])
          [JConstructor k [(x, t)] _] -> do
            t' <- applySubst t
            return (Tyvar i, t')
          [JConstructor k xts _] -> do
            ts' <- mapM (applySubst . snd) xts
            return (Tyvar i, tupleType ts')
          _ -> Nothing
      where
        applySubst :: Type -> Maybe Type
        applySubst t | isBuiltin t = Just t
        applySubst (TCon "List" [t]) = fmap (\t' -> TCon "List" [t']) (applySubst t)
        applySubst (TCon "Maybe" [t]) = fmap (\t' -> TCon "Maybe" [t']) (applySubst t)
        applySubst (TCon t []) = lookup (Tyvar t) subst
        applySubst t = Nothing

    findSubst = case allSubsts of
      []        -> error "no subst possible!"
      allSubsts -> minimumBy (\s1 s2 -> cost s1 `compare` cost s2) allSubsts

    allSubsts :: [Subst]
    allSubsts = do
      let mappings :: [[(Cost, Tyvar, Type)]]
          mappings = map (filter (\(cost, _, _) -> cost < 0.25) . selectSkinType . toType) (jinterfaces jast)
      generateSubsts mappings

    generateSubsts :: [[(Cost, Tyvar, Type)]] -> [Subst]
    generateSubsts ys = swizzle $ map (map (\(cost, i, j) -> (i, j))) ys

    cost :: Subst -> Cost
    cost = sum . map (uncurry computeCost)

    selectSkinType :: Type -> [(Cost, Tyvar, Type)]
    selectSkinType jt =
      map (\(cost, i) -> (cost, i, jt)) (compareSkinTypes jt)

    compareSkinTypes :: Type -> [(Cost, Tyvar)]
    compareSkinTypes jt = do
      let matches = map ((\i -> (computeCost i jt, i)) . toTypeVar) (interfaces skin)
      sortBy (\(cost, i) (cost', i') -> cost `compare` cost') matches

    isubclasses i = map fst $ filter (\(sub, TCon sup []) -> sup == i) $ M.toList ihierarchy
    jsubclasses j = map fst $ filter (\(sub, TCon sup []) -> sup == j) $ M.toList jhierarchy

    -- The cost is the renaming cost + some function of the subclasses of the two types
    computeCost :: Tyvar -> Type -> Cost
    computeCost (Tyvar i) (TCon j [])  = do
      let renamingCost = matchName skin i j
      -- count the number of subclasses of i that match with subclasses of j
      let ijs = liftM2 (,) (isubclasses i) (jsubclasses j)
      let ijcosts = map (uncurry (matchName skin)) ijs
      let ijcount = length (filter (< 0.5) ijcosts)
      renamingCost * if null ijcosts then 1 else 1 - fromIntegral ijcount / fromIntegral (length ijcosts)

-- Copied from Typer!
-- FIXME

-- Mapping from type variables to types
type Subst = [(Tyvar, Type)]

(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = s5
  where
    s3 = [(u, substTy s1 t) | (u,t) <- s2, isNothing (lookup u s1)]
    s4 = do
      u <- map fst s1 `intersect` map fst s2
      case lookup u s2 of
        Just (TVar v) -> return (v, substTy s1 (TVar u))
        Just t        -> return (u, substTy s1 t)
    s5 = s3 ++ s4 ++ s1

merge s1 s2 = s1 @@ s2

mgu :: Type -> Type -> Maybe Subst
mgu (TVar a) (TVar b) | a == b = Just []
mgu (TVar a) (TVar b) | a < b  = Just [(a,TVar b)]
mgu (TVar a) (TVar b) | b < a  = Just [(b,TVar a)]
mgu (TVar a) t                 = Just [(a,t)]
mgu t (TVar a)                 = Just [(a,t)]
mgu (TCon a as) (TCon b bs) | a == b && length as == length bs = foldl merge [] <$> zipWithM mgu as bs
mgu _ _ = Nothing

-- Apply a substitution to a type.
substTy :: Subst -> Type -> Type
substTy s t @ (TVar x)    = fromMaybe t (lookup x s)
substTy s (TCon label ts) = TCon label (map (substTy s) ts)
substTy s TBoh            = TBoh

data Variance = Covariant | Contravariant
  deriving (Show, Eq)

  -- find rules with similar types
  -- Method should map to "declaration"
  -- I think to make this work nicely, we need to loosen the types of the skin grammar
  -- to allow arbitrary declarations at any level.

findTemplates :: SubtypeEnv -> Type -> Type -> State Skin [Template]
findTemplates _ t u | trace ("findTemplate " ++ show t) False = undefined
findTemplates hierarchy t u = do
  tms <- gets templates
  case filter (\(Template parentType childType rhs action) -> parentType == t && childType == u) tms of
    [] -> case supertype hierarchy t of
            Just super -> findTemplates hierarchy super u
            Nothing    -> return []
    tms -> return tms


-- Generate the RHS of a rule given the expression.
-- TODO: add parent type for generating template
generateRhs :: Maybe Type -> SubtypeEnv -> JExp -> State Skin [(Sym, String)]
generateRhs parent _ e | trace ("generateRhs for " ++ show e ++ " with parent " ++ show parent) False = undefined
generateRhs parent hierarchy (JNew es (TCon label [])) = do
  k <- makeKeyword label
  rhs <- mapM (generateRhs parent hierarchy) es
  return $ (Literal k, "_") : concat rhs
generateRhs parent hierarchy (JOp label es t) = do
  k <- makeKeyword label
  rhs <- mapM (generateRhs parent hierarchy) es
  return $ (Literal k, "_") : concat rhs
generateRhs parent hierarchy (JVar x t) = do
  lhs <- findSymbolForType parent Contravariant hierarchy t
  return [(lhs, x)]
generateRhs parent hierarchy (JK label t) = do
  k <- makeKeyword label
  return [(Literal k, "_")]
generateRhs parent hierarchy e =
  error $ "missing case in generateRhs " ++ show e

makeKeyword :: String -> State Skin String
makeKeyword s = do
  let k = map toLower s
  -- don't add the keyword to the tokens list... if we do, findSymbolForType might find it :-)
  -- the pretty printer handles it correctly already
  -- modify (\skin -> skin { tokens = tokens skin ++ [("TOKEN" ++ k, TCon "String" [])] })
  return k

findSymbolForType :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
findSymbolForType parent _ _ t | trace ("findSymbolForType for " ++ show t ++ " parent=" ++ show parent) False = undefined
findSymbolForType parent variance hierarchy t = do
  case parent of
    Just u -> do
      tms <- findTemplates hierarchy u t
      case tms of
        (Template _ _ rhs action:_) -> do
          n <- gets (length . rules) -- use the length of the rules list as a UID generator
          let name = (map toLower (show t)) ++ "_" ++ show n
          let rule = Rule t name rhs action
          addRule rule
          return $ Nonterminal name
        _ -> addRuleForType parent variance hierarchy t
    Nothing -> addRuleForType parent variance hierarchy t

addRuleForType :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
addRuleForType parent variance hierarchy t | trace ("addRule parent=" ++ show parent ++ " t=" ++ show t) False = undefined
addRuleForType parent variance hierarchy t = do
  rs <- gets rules
  ts <- gets tokens
  as <- gets aliases
  let rulesWithRightType = filter (\(Rule rt _ _ _) -> isSubtype hierarchy rt t) rs
  let lhss = nub $ map (\(Rule _ lhs _ _) -> lhs) (trace (show rs) rulesWithRightType)
  let tokensWithRightType = nub $ filter (\(x, rt) -> isSubtype hierarchy rt t) ts
  let token = fmap fst (listToMaybe tokensWithRightType)
  let lhss' = sortOn (\s -> matchNameWithAliases as s (show t)) lhss
  case lhss' of
    (lhs:lhss) -> do
      -- Pick the first rule of the correct type.
      -- We require the skin grammar be written in dominator order!
      return $ Nonterminal lhs
    [] -> case token of
      Just token -> return $ Terminal token
      Nothing    -> createRuleForType parent variance hierarchy t


-- add new rules at the end -- this preserves the invariant that the start rule is first
addRule :: Rule -> State Skin ()
addRule rule = do
  modify (\skin -> skin { rules = rules skin ++ [rule] })

createRuleForType :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
createRuleForType parent variance hierarchy t =
  case t of
    -- TCon "Object" [] -> return $ Terminal "IDENTIFIER"
    -- TODO: use the templates for these.
    TCon "Array" [a] -> createRuleForArray parent variance hierarchy a
    TCon "List" [a] -> createRuleForList parent variance hierarchy a
    TCon label [] -> case variance of
      -- Covariant -> error $ "missing case in findSymbolForType: looking for supertype of " ++ show t
      -- Contravariant -> error $ "missing case in findSymbolForType: looking for subtype of " ++ show t
      Covariant ->
        -- if the type is builtin, generate rules for that type (arrays and lists and maybe)
        -- if the type is not builtin, just return a new Nonterminal
        -- error $ "missing case " ++ show t
        trace ("hierarchy = " ++ show hierarchy) $
          case M.lookup label hierarchy of
            Just s  -> findSymbolForType parent Covariant hierarchy s
            Nothing -> error $ "missing case in findSymbolForType: looking for supertype of " ++ show t
      Contravariant ->
        trace ("hierarchy = " ++ show hierarchy) $
          case map fst $ filter (\(t1,t2) -> t2 == t) (M.toList hierarchy) of
            (s:_) -> findSymbolForType parent Contravariant hierarchy (TCon s [])
            []    -> error $ "missing case in findSymbolForType: looking for subtype of " ++ show t

createRuleForList :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
createRuleForList parent variance hierarchy a = do
  token <- findSymbolForType parent variance hierarchy a
  let t = TCon "List" [a]
  let lp = (Literal "(", "_")
  let rp = (Literal ")", "_")
  let listName = symname token ++ "_list"
  let name = symname token ++ "_list_brackets"
  let list = (Nonterminal listName, "as")
  let one = (token, "a")
  let comma = (Literal ",", "_")
  let rule1 = Rule (TCon "List" [a]) listName [one] (JOp ":" [JVar "a" a, JK "Nil" (TCon "List" [a])] (TCon "List" [a]))
  let rule2 = Rule (TCon "List" [a]) listName [one, comma, list] (JOp ":" [JVar "a" a, JVar "as" (TCon "List" [a])] (TCon "List" [a]))
  let rule3 = Rule t name [lp, list, rp] (JVar "as" t)
  let rule4 = Rule t name [lp, rp] (JK "Nil" t)
  addRule rule1
  addRule rule2
  addRule rule3
  addRule rule4
  return $ Nonterminal name

createRuleForArray :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
createRuleForArray parent variance hierarchy a = do
  list <- findSymbolForType parent variance hierarchy (TCon "List" [a])
  let t = TCon "Array" [a]
  let name = symname list ++ "_array"
  let rule = Rule t name [(list, "as")] (JOp "listToArray" [JVar "as" (TCon "List" [a])] t)
  addRule rule
  return $ Nonterminal name

parseAndCheck p filename = do
  r <- parseFromFile p filename
  case r of
    Left err ->
      error $ "could not parse " ++ filename ++ ": " ++ show err
    Right tree ->
      return tree

makeNewRules :: [MatchResult] -> SubtypeEnv -> State Skin ()
makeNewRules matchResults hierarchy = do
  forM_ matchResults $ \r -> case r of
    NoMatch e -> do
      Nonterminal lhs <- findSymbolForType Nothing Covariant hierarchy (typeof e)
      rhs <- generateRhs (Just (typeof e)) hierarchy e
      let t = case typeof e of
                TCon label [] ->
                  case M.lookup label hierarchy of
                    Just t -> t
                    Nothing -> TCon label []
                t -> t
      let rule = Rule t lhs rhs e
      addRule rule
      return ()
    _ -> return ()
  return ()

main :: IO ()
main = do
  -- Parse arguments
  args <- getArgs
  when (length args /= 2) $ error "usage: cat skin-file ast-file"

  let skinFile = head args
  let astFile = head (tail args)

  run skinFile astFile

-- factor out the core of main so we can call it from the repl more easily
run :: String -> String -> IO ()
run skinFile astFile = do

  -- read the skin and the java AST files
  skin <- parseAndCheck skin skinFile
  jast <- parseAndCheck javaAST astFile

  debug $ "skin: " ++ show skin
  debug $ "Java AST:\n" ++ show jast

  typedSkin <- typeCheckSkin skin
  typedJast <- typeCheckJAST jast

  debug $ "Typed Java AST:\n" ++ show typedJast

  -- match types between the skin and the JAST, rewriting the skin
  -- to use the JAST types.
  matchedSkin <- matchTypes typedSkin typedJast
  debug $ "matchedSkin: " ++ show matchedSkin

  putStrLn "original rules (with types subst'ed)"
  forM_ (rules matchedSkin) print
  putStrLn "<< original rules (with types subst'ed)"

  -- Type-check again... This is just a sanity check that matchTypes didn't mess up the types
  typeCheckSkin matchedSkin

  let hierarchy = makeHierarchy (jinterfaces typedJast) []

  let jcalls = jexps typedJast
  debug $ "jcalls:\n" ++ intercalate "\n" (map show jcalls)

  debug "Matching AST with skin:"
  matchResults <- forM jcalls $ \k -> case k of
    JNew args t ->
      return $ runReader (matchConstructors k) (matchedSkin, hierarchy)
    _ ->
      return $ NoMatch k

  putStrLn "factories"
  forM_ (filter isMatch matchResults) print
  putStrLn "<< factories"

  -- For each unmatched constructor call, for each subexpression of the
  -- call, make sure there is a grammar rule for that subexpression's type.

  -- newRules <- forM [e | NoMatch e <- matchResults] $ generateRulesForSubexpressions

  -- For each unmatched constructor, generate a new factory method and generate a new rule that invokes that method.

  -- Unlike when matching, include the constructors in the subtype hierarchy when generating new rules.
  let hierarchyWithConstructors = makeHierarchy (jinterfaces typedJast) (jconstructors typedJast)
  let skinWithNewRules = execState (makeNewRules matchResults hierarchyWithConstructors) matchedSkin

  putStrLn "new rules"
  forM_ (rules skinWithNewRules) print
  putStrLn "<< new rules"

  putStrLn "removed unused rules"
  let reducedSkin = skinWithNewRules { rules = removeUnusedRules matchResults (rules skinWithNewRules) }
  putStrLn "<< removed unused rules"

  putStrLn "without unused rules"
  forM_ (rules reducedSkin) print
  putStrLn "<< without unused rules"

  let g = Grammar {
    gheader = jheader jast,
    gbody = jbody jast,
    grules = rules reducedSkin,
    gfactories = mapMaybe matchToFactory matchResults,
    gtokens = nub $ tokens reducedSkin ++ concatMap ruleTokens (rules reducedSkin)
  }

  putStrLn "grammar"
  putStr (pp g)
  putStrLn "<<grammar"

  return ()

loadAliases :: String -> IO [[String]]
loadAliases file = aliases <$> parseAndCheck skin file

ruleTokens (Rule t lhs rhs e) = mapMaybe rhsToken rhs
  where
    rhsToken (Literal a, _) = Just (literalToToken a, TCon "String" [])
    rhsToken _ = Nothing

data Grammar = Grammar { gheader :: String, gbody :: String, grules :: [Rule], gfactories :: [JFactory], gtokens :: [(String, Type)] }
  deriving Show

type JFactory = (JConstructor, JExp)

matchToFactory (Match _ k e) = Just (k, e)
matchToFactory _ = Nothing

class PP a where
  pp :: a -> String

ppTerminalDeclarations tokens rules = nub $ mapMaybe go tokens
  where
    go (x, t) = Just $ "terminal skinner.lex.Token<" ++ ppBox t ++ "> " ++ x ++ ";"
    -- go (Rule t lhs rhs _) = mapMaybe go' rhs
    -- go' (Terminal a, _) = lookup a tokens >>= \t -> Just $ "terminal " ++ pp t ++ " " ++ a ++ ";"
    -- go' (Literal a, _) = Just $ "terminal String " ++ (literalToToken a) ++ ";"
    -- go' _ = Nothing

ppNonterminalDeclarations rules = nub $ map go rules
  where
    go (Rule (TCon "void" []) lhs rhs _) = "non terminal Object " ++ lhs ++ ";"
    go (Rule t lhs rhs _) = "non terminal " ++ pp t ++ " " ++ lhs ++ ";"

ppBox t = case boxedType t of
  Just t' -> pp t'
  Nothing -> pp t

literalToToken s = "TOKEN" ++ join (map go s)
  where
    go '(' = "_LPAREN"
    go ')' = "_RPAREN"
    go '{' = "_LBRACE"
    go '}' = "_RBRACE"
    go '[' = "_LBRACK"
    go ']' = "_RBRACK"
    go '<' = "_LT"
    go '>' = "_GT"
    go '=' = "_EQ"
    go '.' = "_DOT"
    go ',' = "_COMMA"
    go '?' = "_QUESTION"
    go '!' = "_BANG"
    go '\'' = "_SQUOT"
    go '`' = "_BQUOT"
    go '\"' = "_DQUOT"
    go '$' = "_DOLLAR"
    go '@' = "_AT"
    go '%' = "_PERCENT"
    go '^' = "_CARET"
    go '&' = "_AND"
    go '*' = "_STAR"
    go '-' = "_DASH"
    go '_' = "_UNDERSCORE"
    go '+' = "_PLUS"
    go '\\' = "_BACKSLASH"
    go '/' = "_SLASH"
    go '|' = "_BAR"
    go ';' = "_SEMI"
    go ':' = "_COLON"
    go '~' = "_TWIDDLE"
    go c = [c]

-- TODO: goal rule gets deleted
-- TODO: eliminate rules with dead nonterminals on the rhs
instance PP Grammar where
  pp g = unlines $
                 ["// Grammar generated by Skinner."
                 ,""
                 ,"import java_cup.runtime.Symbol;"
                 ,"import skinner.util.Position;"
                 ,"import skinner.util.Tuple2;"
                 ,"import skinner.util.Tuple3;"
                 ,"import skinner.lex.*;"
                 ,"import java.util.List;"
                 ,"import java.util.ArrayList;"
                 ,"import java.util.Collections;"
                 ,gheader g
                 ,""
                 ,"parser Parser extends java_cup.runtime.lr_parser {:"
                 ,"    public Parser(Lexer l) {"
                 ,"        super();"
                 ,"        lexer = l;"
                 ,"    }"
                 ,""
                 ,"    Lexer lexer;"
                 ,""
                 ,"    // use two positions, since the parser does one token lookahead"
                 ,"    Position prev_pos, position;"
                 ,""
                 ,"    public Symbol nextSymbol() throws java.io.IOException {"
                 ,"        Token t = lexer.nextToken();"
                 ,"        position = prev_pos;"
                 ,"        prev_pos = t.getPosition();"
                 ,"        return new Symbol(t.symbol(), t);"
                 ,"    }"
                 ,""
                 ,gbody g
                 ,""
                 ]
                 ++ library
                 ++ [""]
                 ++ map pp (gfactories g)
                 ++ [":}"]
                 ++ ["scan with {: return nextSymbol(); :};"]
                 ++ [""]
                 ++ ppTerminalDeclarations (gtokens g) (grules g)
                 ++ [""]
                 ++ ppNonterminalDeclarations (grules g)
                 ++ [""]
                 ++ ["start with goal;"]
                 ++ [""]
                 ++ map pp (map (fixTerminals (gtokens g)) (grules g))

fixTerminals tokens (Rule t lhs rhs e) = Rule t lhs rhs (fixExp e)
  where
    fixExp (JOp op es t) = JOp op (map fixExp es) t
    fixExp (JNew es t) = JNew (map fixExp es) t
    fixExp (JK k t) = JK k t
    fixExp (JVar x t) =
        if isTokenVar x
          then JOp "getValue" [JVar x (TCon "Token" [t])] t
          else JVar x t

    isTokenVar x = foldl (isTokenRhs x) False rhs
    isTokenRhs x v (Nonterminal _, y) = v
    isTokenRhs x v (Terminal _, y)    = v || x == y
    isTokenRhs x v (Literal _, y)     = v || x == y


library :: [String]
library =
  ["    <T> List<T> consList(T x, List<T> xs) { List<T> ys = new ArrayList<T>(); ys.add(x); ys.addAll(xs); return ys; }"
  ,"    <T> List<T> appendLists(List<T> xs, List<T> ys) { List<T> zs = new ArrayList<T>(); zs.addAll(xs); zs.addAll(ys); return zs; }"
  ]

instance PP Rule where
  pp (Rule (TCon "void" []) lhs rhs e) =
        lhs ++ " ::= " ++ intercalate " " (map pp rhs) ++ "\n        {: RESULT = null; :}\n    ;\n"
  pp (Rule t lhs rhs e) = lhs ++ " ::= " ++ intercalate " " (map pp rhs) ++ "\n        {: RESULT = " ++ pp e ++ "; :}\n    ;\n"

instance PP (Sym, String) where
  pp (Nonterminal a, "_") = a
  pp (Terminal a, "_") = a
  pp (Literal a, "_") = literalToToken a
  pp (Nonterminal a, x) = a ++ ":" ++ x
  pp (Terminal a, x) = a ++ ":" ++ x
  pp (Literal a, x) = literalToToken a ++ ":" ++ x

instance PP (String, Type) where
  pp (x, t) = pp t ++ " " ++ x

instance PP JExp where
  pp (JOp "long2int" [e] t) = "((int)" ++ pp e ++ ")"
  pp (JOp "float2int" [e] t) = "((int)" ++ pp e ++ ")"
  pp (JOp "double2int" [e] t) = "((int)" ++ pp e ++ ")"
  pp (JOp "int2float" [e] t) = "((float)" ++ pp e ++ ")"
  pp (JOp "long2float" [e] t) = "((float)" ++ pp e ++ ")"
  pp (JOp "double2float" [e] t) = "((float)" ++ pp e ++ ")"
  pp (JOp "int2long" [e] t) = "((long)" ++ pp e ++ ")"
  pp (JOp "float2long" [e] t) = "((long)" ++ pp e ++ ")"
  pp (JOp "double2long" [e] t) = "((long)" ++ pp e ++ ")"
  pp (JOp "float2double" [e] t) = "((double)" ++ pp e ++ ")"
  pp (JOp "int2double" [e] t) = "((double)" ++ pp e ++ ")"
  pp (JOp "long2double" [e] t) = "((double)" ++ pp e ++ ")"
  pp (JOp "unbox_int" [e] t) = "((int)" ++ pp e ++ ")"
  pp (JOp "unbox_long" [e] t) = "((long)" ++ pp e ++ ")"
  pp (JOp "unbox_float" [e] t) = "((float)" ++ pp e ++ ")"
  pp (JOp "unbox_double" [e] t) = "((double)" ++ pp e ++ ")"
  pp (JOp "box_int" [e] t) = "((Integer)" ++ pp e ++ ")"
  pp (JOp "box_long" [e] t) = "((Long)" ++ pp e ++ ")"
  pp (JOp "box_float" [e] t) = "((Float)" ++ pp e ++ ")"
  pp (JOp "box_double" [e] t) = "((Double)" ++ pp e ++ ")"
  pp (JOp "charToString" [e] t) = "(\"\" " ++ pp e ++ ")"
  pp (JOp "stringToChar" [e] t) = pp e ++ ".charAt(0)"
  pp (JOp "size" [e] t) = pp e ++ ".size()"
  pp (JOp "isEmpty" [e] t) = pp e ++ ".isEmpty()"
  pp (JOp "length" [e] t) = pp e ++ ".length"
  pp (JOp "getValue" [e] t) = pp e ++ ".getValue()"
  pp (JOp "Just" [e] t) = pp e
  pp (JK "()" t) = "null"
  pp (JK "Nothing" t) = "null"
  pp (JK "Nil" (TCon _ [base])) = "java.util.Collections.<" ++ pp base ++ ">emptyList()"
  pp (JNew es t) = "new " ++ pp t ++ "(" ++ intercalate ", " (map pp es) ++ ")"
  pp (JVar x t) = x
  pp (JOp ":" es t) = "parser.consList" ++ "(" ++ intercalate ", " (map pp es) ++ ")"
  pp (JOp "++" es t) = "parser.appendLists" ++ "(" ++ intercalate ", " (map pp es) ++ ")"
  pp (JOp "toMaybe" [e] (TCon _ [base])) | isPrimitive base = "((" ++ pp (fromJust (boxedType base)) ++ ") " ++ pp e ++ ")"
  pp (JOp "toMaybe" [e] (TCon _ [base])) = pp e
  pp (JOp "unMaybe" [e] (base)) | isPrimitive base = "((" ++ pp base ++ ") " ++ pp e ++ ")"
  pp (JOp "unMaybe" [e] (base)) = pp e
  pp (JOp "maybeToList" [e] (TCon _ [base])) = "java.util.Collections.<" ++ pp base ++ ">singletonList(" ++ pp e ++ ")"
  pp (JOp "listToArray" [e] (TCon _ [base])) = pp e ++ ".toArray(new " ++ pp base ++ "[0])"
  pp (JOp "arrayToList" [e] (TCon _ [base])) = "java.util.Arrays<" ++ pp base ++ ">asList(" ++ pp e ++ ")"
  pp (JOp "toArray2" [e1, e2] (TCon _ [base])) = "new " ++ pp base ++ "[] { " ++ pp e1 ++ ", " ++ pp e2 ++ "}"
  pp (JOp "toList2" [e1, e2] (TCon _ [base])) = "java.util.Arrays.<" ++ pp base ++ ">asList(new " ++ pp base ++ "[] { " ++ pp e2 ++ ", " ++ pp e2 ++ " })"
  pp (JOp x es t) = "parser." ++ x ++ "(" ++ intercalate ", " (map pp es) ++ ")"
  pp (JK k t) = k

boxPrimitive t | isPrimitive t = fromJust (boxedType t)
boxPrimitive t                 = t

instance PP Type where
  pp (TCon "Maybe" [t]) = pp (boxPrimitive t)
  pp (TCon "Array" [t]) = pp t ++ "[]"
  pp (TCon "(,)" ts) = pp (TCon "Tuple2" ts)
  pp (TCon "(,,)" ts) = pp (TCon "Tuple3" ts)
  pp (TCon label []) = label
  pp (TCon label ts) = label ++ "<" ++ intercalate ", " (map (pp . boxPrimitive) ts) ++ ">"
  pp (TVar (Tyvar v)) = v

instance PP (JConstructor, JExp) where
  pp (JConstructor name args super, e) = "    " ++ pp super ++ " " ++ name ++ "(" ++ intercalate ", " (map pp args) ++ ") {\n        return " ++ pp e ++ ";\n    }\n"
