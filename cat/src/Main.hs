module Main (main) where

import           Control.Applicative  ((*>), (<$), (<$>), (<*), (<*>))
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Char            (isLower, isUpper, toLower, toUpper)
import           Data.List            (find, intercalate, minimum, minimumBy,
                                       nub, sortBy, sortOn, (\\))
import           Data.Maybe           (catMaybes, fromMaybe, listToMaybe)
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
-- import TreeMatch3
-- import Synth

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

freeVars :: JExp -> [(String, Type)]
freeVars (JNew es t)   = nub $ concatMap freeVars es
freeVars (JOp op es t) = nub $ concatMap freeVars es
freeVars (JK k t)      = []
freeVars (JVar x t)    = [(x, t)]

class Wordy a where
  toBagOfWords :: a -> [String]

instance Wordy JExp where
  toBagOfWords (JNew es t)   = toBagOfWords t ++ concatMap toBagOfWords es
  toBagOfWords (JOp op es t) = toBagOfWords t
  toBagOfWords (JK k t)      = k : toBagOfWords t
  toBagOfWords (JVar x t)    = toBagOfWords t    -- NOTE: do not include the variable name

instance Wordy Type where
  toBagOfWords (TCon label []) = [label]
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

coerce :: SubtypeEnv -> JExp -> Type -> Maybe JExp
coerce hierarchy e t = go (typeof e) t
  where
    -- s <: t
    go s t | subtype hierarchy s t = Just e

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

    -- List[void] --> int
    -- Array[void] --> int
    -- Maybe[void] --> boolean
    go (TCon "List" [TCon "void" []]) (TCon "int" []) = Just $ JOp "size" [e] t
    go (TCon "Array" [TCon "void" []]) (TCon "int" []) = Just $ JOp "size" [e] t
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

    -- t -> List[t]
    go s (TCon "List" [w]) | s == w = Just $ JOp "toList1" [e] t
    -- t -> Array[t]
    go s (TCon "Array" [w]) | s == w = Just $ JOp "toArray1" [e] t
    -- List[t] -> Array[t]
    go (TCon "List" [u]) (TCon "Array" [w]) | u == w = Just $ JOp "listToArray" [e] t
    -- Array[t] -> List[t]
    go (TCon "Array" [u]) (TCon "List" [w]) | u == w = Just $ JOp "arrayToList" [e] t
    -- Maybe[t] -> List[t]
    go (TCon "Maybe" [u]) (TCon "List" [w]) | u == w = Just $ JOp "maybeToList" [e] t
    -- Maybe[t] -> t
    go (TCon "Maybe" [u]) t | u == t && isNullable t = Just $ JOp "unMaybe" [e] t
    -- t -> Maybe[t]
    go s (TCon "Maybe" [w]) | s == w = Just $ JOp "toMaybe" [e] t

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
  debug $ "match constructors vs " ++ show new

  (skin, hierarchy) <- ask

  let fv = freeVars new

  rs <- forM (factories skin) $ \k @ (JConstructor skinLabel skinFields skinSuper) -> do

    theta <-  -- trace ("matching " ++ show k ++ " with " ++ show new) $ do
      case (skinFields, fv) of
        -- HACK: if there are more parameter to the factory than there are free variables in
        -- the constructor call, try to tuple up the parameters
        ([(y1, t1'), (y2, t2')], [(x, TCon "List" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "toList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) (TCon "List" [t]) of
            Just e  -> return [(x, e)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, TCon "Array" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "toArray2" [JVar y1 t1', JVar y2 t1'] (TCon "Array" [t1'])) (TCon "Array" [t]) of
            Just e  -> return [(x, e)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, t)]) | t1' == t2' ->
          case coerce hierarchy (JOp "toList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) t of
            Just e  -> return [(x, e)]
            Nothing -> return []

        (skinFields, fv) | length skinFields == length fv -> do

          -- We have a call to a constructor in the J AST.
          -- We want to see if we can invoke that constructor from the given factory method in the Skin.

          -- To do this, we see if we can coerce each of the parameters of the factory method
          -- into an argument of the constructor call.

          -- We need to cover all arguments to the constructor call (i.e., those that are freeVars of the `new` JExp).

          -- We just assume the free variables and factory parameters are in the same order. This could be relaxed when the types are different.

          otheta <- forM (zip fv skinFields) $ \((x, t), (y, t')) -> -- trace ("coerce " ++ show (y, t') ++ " to " ++ show t) $
            case coerce hierarchy (JVar y t') t of
              Just e  -> return $ Just (x, e)
              Nothing -> return Nothing

          let theta = catMaybes otheta

          return theta
        _ ->
          return []

    if length theta == length fv
      then do
        let cost = minimum $ map (matchName skin skinLabel) (toBagOfWords new)
        return [(cost, k, substVars theta new)]
      else
        return []

  case sortOn (\(a,b,c) -> a) (concat rs) of
    ((a,b,c):rs) -> return $ Match a b c
    _            -> return $ NoMatch new

matchConstructors e = return $ NoMatch e


type SubtypeEnv = [(Type, Type)]

supertype :: SubtypeEnv -> Type -> Maybe Type
supertype env (TVar x)           = Nothing
supertype env (TCon "Object" []) = Nothing
supertype env t                  = lookup t env

subtype :: SubtypeEnv -> Type -> Type -> Bool
subtype env t1 (TCon "Object" []) = True
subtype env t1 t2 | t1 == t2 = True
subtype env t1 t2 = case supertype env t1 of
                   Nothing -> False
                   Just t  -> subtype env t t2

generateHierarchy :: JAST -> SubtypeEnv
generateHierarchy jast = [(TCon label [], super) | JInterface label super <- jinterfaces jast]
                       ++ [(TCon label [], super) | JConstructor label _ super <- jconstructors jast]

generateSkinHierarchy :: Skin -> SubtypeEnv
generateSkinHierarchy skin = []

generateFactoryCalls :: JAST -> [JExp]
generateFactoryCalls jast = concatMap instConstructor (jconstructors jast)
  where
    instConstructor :: JConstructor -> [JExp]
    instConstructor (JConstructor label fields super) = [JNew es (TCon label []) | es <- expandEnums jast fields]

    expandEnums :: JAST -> [(String, Type)] -> [[JExp]]
    expandEnums jast xts = go (jenums jast) [map (uncurry JVar) xts]
      where
        go :: [JEnum] -> [[JExp]] -> [[JExp]]
        go [] ess       = removeEnumVars ess
        go (e:rest) ess = go rest (addEnum e ess)

        removeEnumVars ess = filter (not . hasEnumVars) ess
        hasEnumVars es = any isEnumVar es
        isEnumVar ex = any (`isThisEnumVar` ex) (jenums jast)
        isThisEnumVar (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = True
        isThisEnumVar _ _ = False

        addEnum :: JEnum -> [[JExp]] -> [[JExp]]
        addEnum e ess = concatMap (addEnum1 e) ess

        addEnum1 :: JEnum -> [JExp] -> [[JExp]]
        addEnum1 e es = nub $ [map (addEnum2 e) es, es]

        addEnum2 :: JEnum -> JExp -> JExp
        addEnum2 (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = JK enum (TCon label [])
        addEnum2 _ ex = ex

matchName :: Skin -> String -> String -> Int
matchName skin = matchNameWithAliases (aliases skin)

-- match types in the skin to types in the JAST, rewriting the skin
-- FIXME: currently this works by matching names using only aliases with no forgiveness
-- Also, it maps more than one skin type to the same JAST type, which may be broken (but might not be...)
-- Should, for instance, map both skin Stm and Exp to JAST Expr.
-- TODO: map unmapped types to Void and prune the actions and collapse types.
-- Thus, for an untyped language, want to map Formal to (Type,String) to (void,String) to String.
-- Mapping should perform coercions too... we should combine all this with the factory/constructor mapping.
matchTypes :: Monad m => Skin -> JAST -> m Skin
matchTypes skin jast = do
  debug "match types"
  let is = interfaces skin
  let js = jinterfaces jast
  let match2 (j @ (JInterface label _)) (i @ (JInterface skinLabel _)) =
         let cost = matchName skin skinLabel label
           in (cost, i, j)

  -- Make a substitution with the exact matches.
  let ks = filter (\(cost, _, _) -> cost <= 0) $ liftM2 match2 js is
  let substToVoid = map (\i -> (i, JInterface "void" (TCon "Object" []))) is
  debug $ show $ take 10 $ sortOn (\(a,b,c) -> a) ks
  return $ substSkin (map (\(cost, i, j) -> (i, j)) ks ++ substToVoid) skin

  where
    substSkin s skin = skin { interfaces = substInterfaces s (interfaces skin),
                              factories = substCtors s (factories skin),
                              rules = substRules s (rules skin),
                              tokens = substTokens s (tokens skin),
                              templates = substTemplates s (templates skin) }


    substTemplates s js = map (substTemplate s) js
    substTemplate s (Template t1 t2 rhs action) = Template (substType s t1) (substType s t2) rhs action

    substTokens s js = map (substToken s) js
    substToken s (x, t) = (x, substType s t)

    substInterfaces s js = map (substInterface s) js
    substInterface s (JInterface label super) = JInterface (substLabel s label) (substType s super)

    substCtors s js = map (substCtor s) js
    substCtor s (JConstructor label fields super) = JConstructor label (substFields s fields) (substType s super)

    substRules s js = map (substRule s) js
    substRule s (Rule typ label rhs e) = Rule (substType s typ) label rhs e

    substFields s fields = map (substField s) fields
    substField s (x,t) = (x, substType s t)

    substType s (TCon label ts) = TCon (substLabel s label) (map (substType s) ts)
    substType s (TCon label ts) = TCon (substLabel s label) (map (substType s) ts)
    substType s (TVar x) = TVar x

    substLabel [] label = label
    substLabel ((JInterface old _, JInterface new _):rest) label
      | label == old = new
      | otherwise    = substLabel rest label

removeUnreachableRules :: [Rule] -> [Rule]
removeUnreachableRules rules = rules  -- remove rules unreachable from the start symbol
                                      -- TODO TODO TODO

data MatchResult = Match Int JConstructor JExp
                 | NoMatch JExp
  deriving Show

findRules :: Skin -> [JConstructor] -> [Rule]
findRules skin ks = filter (ruleInvokes ks) (rules skin)
  where
    ruleInvokes ks (Rule t lhs rhs e) = expInvokes ks e

    expInvokes ks (JVar x t)    = True
    expInvokes ks (JK k t)      = True
    expInvokes ks (JNew es t)   = matches t ks && all (expInvokes ks) es
    expInvokes ks (JOp op es t) = all (expInvokes ks) es

    matches (TCon "List" [t]) ks = matches t ks
    matches (TCon "Maybe" [t]) ks = matches t ks
    matches (TCon "Array" [t]) ks = matches t ks
    matches (TCon "String" []) _ = True
    matches (TCon "java.lang.Void" []) _ = True
    matches (TCon "java.lang.Boolean" []) _ = True
    matches (TCon "java.lang.Character" []) _ = True
    matches (TCon "java.lang.Byte" []) _ = True
    matches (TCon "java.lang.Short" []) _ = True
    matches (TCon "java.lang.Integer" []) _ = True
    matches (TCon "java.lang.Long" []) _ = True
    matches (TCon "java.lang.Float" []) _ = True
    matches (TCon "java.lang.Double" []) _ = True
    matches t _ | isPrimitive t = True
    matches (TCon label []) ks = any (\(JConstructor label' _ _) -> label == label') ks

data Variance = Subtype | Supertype
  deriving (Show, Eq)

-- Find an appropriate LHS for the given expression.
findAppropriateLhs :: SubtypeEnv -> JExp -> State Skin Sym
findAppropriateLhs hierarchy e = findLhsForType Supertype hierarchy (typeof e)

  -- find rules with similar types
  -- Method should map to "declaration"
  -- I think to make this work nicely, we need to loosen the types of the skin grammar
  -- to allow arbitrary declarations at any level.

-- Generate the RHS of a rule given the expression.
-- TODO: add parent type for generating template
generateRhs :: SubtypeEnv -> JExp -> State Skin [(Sym, String)]
generateRhs hierarchy (JNew es (TCon label [])) = do
  k <- makeKeyword label
  rhs <- mapM (generateRhs hierarchy) es
  return $ (Terminal k, "_") : concat rhs
generateRhs hierarchy (JVar x t) = do
  lhs <- findLhsForType Subtype hierarchy t
  return [(lhs, x)]

makeKeyword :: String -> State Skin String
makeKeyword s = do
  let k = map toLower s
  modify (\skin -> skin { tokens = nub $ (k, TCon "void" []) : tokens skin })
  return k

findLhsForType :: Variance -> SubtypeEnv -> Type -> State Skin Sym
findLhsForType variance hierarchy t = do
  rs <- gets rules
  ts <- gets tokens
  let rulesWithRightType = filter (\(Rule rt _ _ _) -> subtype hierarchy rt t) rs
  let lhss = nub $ map (\(Rule _ lhs _ _) -> lhs) (trace (show rs) rulesWithRightType)
  let tokensWithRightType = nub $ filter (\(x, rt) -> subtype hierarchy rt t) ts
  let token = fmap fst (listToMaybe tokensWithRightType)
  case lhss of
    (lhs:_) -> return $ Nonterminal lhs
    [] -> case token of
      Just token -> return $ Terminal token
      Nothing    -> case t of
                      -- TCon "Object" [] -> return $ Terminal "IDENTIFIER"
                      TCon "String" [] -> return $ Terminal "IDENTIFIER"
                      TCon "int" [] -> return $ Terminal "INT_LITERAL"
                      TCon "Array" [a] -> do
                        list <- findLhsForType variance hierarchy (TCon "List" [a])
                        let name = symname list ++ "_array"
                        let rule = Rule t name [(list, "as")] (JOp "listToArray" [JVar "as" (TCon "List" [a])] t)
                        modify (\skin -> skin { rules = rule : rules skin })
                        return $ Nonterminal name
                      TCon "List" [a] -> do
                        token <- findLhsForType variance hierarchy a
                        let lp = (Terminal "(", "_")
                        let rp = (Terminal ")", "_")
                        let listName = symname token ++ "_list"
                        let name = symname token ++ "_list_brackets"
                        let list = (Nonterminal listName, "as")
                        let one = (token, "a")
                        let comma = (Terminal ",", "_")
                        let rule1 = Rule (TCon "List" [a]) listName [one] (JOp ":" [JVar "a" a, JK "Nil" (TCon "List" [a])] (TCon "List" [a]))
                        let rule2 = Rule (TCon "List" [a]) listName [one, comma, list] (JOp ":" [JVar "a" a, JVar "as" (TCon "List" [a])] (TCon "List" [a]))
                        let rule3 = Rule t name [lp, list, rp] (JVar "as" t)
                        let rule4 = Rule t name [lp, rp] (JK "Nil" t)
                        modify (\skin -> skin { rules = rule1 : rule2 : rule3 : rule4 : rules skin })
                        return $ Nonterminal name
                      t -> case variance of
                        Subtype -> do
                          -- if the type is builtin, generate rules for that type (arrays and lists and maybe)
                          -- if the type is not builtin, just return a new Nonterminal
                          -- error $ "missing case " ++ show t
                          trace ("hierarchy = " ++ show hierarchy) $
                            case lookup t hierarchy of
                              Just s  -> findLhsForType Subtype hierarchy s
                              Nothing -> error $ "missing case " ++ show t
                        Supertype -> do
                          -- FIXME
                          trace ("hierarchy = " ++ show hierarchy) $
                            case map fst $ filter (\(t1,t2) -> t2 == t) hierarchy of
                              (s:_) -> findLhsForType Supertype hierarchy s
                              []    -> error $ "missing case " ++ show t


parseAndCheck p filename = do
  r <- parseFromFile p filename
  case r of
    Left err ->
      error $ "could not parse " ++ filename ++ ": " ++ show err
    Right tree ->
      return tree

makeNewRules :: [MatchResult] -> SubtypeEnv -> State Skin ()
makeNewRules matchResults hierarchy = do
  forM matchResults $ \r -> case r of
    NoMatch e -> do
      rhs <- generateRhs hierarchy e
      Nonterminal lhs <- findAppropriateLhs hierarchy e
      let rule = Rule (typeof e) lhs rhs e
      modify (\skin -> skin { rules = rule : (rules skin) })
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

  -- read the skin and the java AST files
  skin <- parseAndCheck skin skinFile
  jast <- parseAndCheck javaAST astFile

  debug $ "skin: " ++ show skin
  debug $ "Java AST:\n" ++ show jast

  typedSkin <- typeCheckSkin skin

  -- match types between the skin and the JAST, rewriting the skin
  -- to use the JAST types.
  skin' <- matchTypes typedSkin jast
  debug $ "skin': " ++ show skin'

  -- Type-check again... This is just a sanity check that matchTypes didn't mess up the types
  typeCheckSkin skin'

  let hierarchy = generateHierarchy jast ++ generateSkinHierarchy skin'

  let jcalls = generateFactoryCalls jast
  debug $ "jcalls:\n" ++ intercalate "\n" (map show jcalls)

  debug "Matching AST with skin:"
  matchResults <- forM jcalls $ \k -> case k of
    JNew args t ->
      return $ runReader (matchConstructors k) (skin', hierarchy)
    _ ->
      return $ NoMatch k

  forM_ matchResults print

  -- For each unmatched constructor call, for each subexpression of the
  -- call, make sure there is a grammar rule for that subexpression's type.

  -- newRules <- forM [e | NoMatch e <- matchResults] $ generateRulesForSubexpressions

  -- For each unmatched constructor, generate a new factory method and generate a new rule that invokes that method.

  forM_ (rules skin') print

  let skin'' = execState (makeNewRules matchResults hierarchy) skin'

  forM_ (rules skin'') print

  -- Need to prune the grammar.
  -- Starting at root symbol ("goal")
  -- eliminate rhs symbols that aren't covered by the factory calls

{-
  -- To synthesize a rule from a Java constructor:
  -- First: rule placement (what's the LHS?)
  -- Second: Syntax... "learn" the syntax for an Exp with a Type child, a Stm with a Exp child, etc.

  -- match the skin AST with the Java AST
  let (cost, caseMatches, typeMatches) = matchConstructorsToSkinAST skin javaConstructors
  debug $ "cost " ++ show cost
  debug $ "case " ++ intercalate "\n" (map show caseMatches)
  debug $ "type " ++ intercalate "\n" (map show typeMatches)

  -- generate new rules
  newRules <- generateNewRules javaConstructors caseMatches
  debug $ "new rules = " ++ show newRules

  let simp (ctor, c) = [(ctor, c, TCon "void" [])]
      modelMap = concatMap simp caseMatches

  debug "new grammar"

  forM_ (rules skin ++ newRules) $ \(Rule t lhs rhs action) -> do
      case synthFromModel action t modelMap of
        Nothing -> return ()
        Just x -> do
          debug $ "RULE"
          debug $ "  " ++ lhs ++ " ::= " ++ show rhs
          debug $ "  " ++ show action ++ " :: " ++ show t
          debug $ "  " ++ x
-}

  let skin'' = skin { rules = removeUnreachableRules (rules skin') }

  return ()
