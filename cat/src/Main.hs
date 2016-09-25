module Main (main) where

import           Control.Applicative  ((*>), (<$), (<$>), (<*), (<*>))
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Char            (isLower, isUpper, toLower, toUpper)
import           Data.List            (find, intercalate, minimum, minimumBy,
                                       nub, sortBy, sortOn, (\\), permutations)
import qualified Data.Map             as M
import           Data.Maybe           (catMaybes, fromMaybe, listToMaybe)
import           Data.Monoid
import           Data.Tuple           (swap)

import           Debug.Trace          (trace)

import           System.Environment   (getArgs)
import           System.Random

import           Text.Parsec          (parse)
import           Text.Parsec.String

import           Aliases
import           AST
import           JASTParse
import           SkinParse
import           Typer

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

          -- We have a call to a constructor in the Java AST.
          -- We want to see if we can invoke that constructor from the given factory method in the Skin.

          -- To do this, we see if we can coerce each of the parameters of the factory method
          -- into an argument of the constructor call.

          -- We need to cover all arguments to the constructor call (i.e., those that are free variables of the `new` JExp).

          -- We just assume the free variables and factory parameters are in the same order. This could be relaxed when the types are different.
          -- In particular, we might have a separate enum parameter that (e.g., PLUS on a BinaryExpression node) that could go anywhere in the parameter list.

          -- TOOD: we need to handle extra arguments like a Position.

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

        removeEnumVars = filter (not . hasEnumVars)
        hasEnumVars = any isEnumVar
        isEnumVar ex = any (`isThisEnumVar` ex) (jenums jast)
        isThisEnumVar (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = True
        isThisEnumVar _ _ = False

        addEnum :: JEnum -> [[JExp]] -> [[JExp]]
        addEnum e = concatMap (addEnum1 e)

        addEnum1 :: JEnum -> [JExp] -> [[JExp]]
        addEnum1 e es = nub [map (addEnum2 e) es, es]

        addEnum2 :: JEnum -> JExp -> JExp
        addEnum2 (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = JK enum (TCon label [])
        addEnum2 _ ex = ex

matchName :: Skin -> String -> String -> Int
matchName skin = matchNameWithAliases (aliases skin)

-- match types skinhe JAST, rewriting the skin
-- FIXME: currently this works by matching names using only aliases with no forgiveness
-- Also, it maps more than one skin type to the same JAST type, which may be broken (but might not be...)
-- Should, for instance, map both skin Stm and Exp to JAST Expr.
-- TODO: map unmapped types to Void and prune the actions and collapse types.
-- Thus, for an untyped language, want to map Formal to (Type,String) to (void,String) to String.
-- Mapping should perform coercions too... we should combine all this with the factory/constructor mapping.
matchTypes :: Skin -> JAST -> IO Skin
matchTypes skin jast = do
  let randomList seed = randoms (mkStdGen seed) :: [Probability]
  seed <- randomIO

  putStrLn "new type matcher"
  let mapping = matchTypesMetropolis (randomList seed) skin jast
  print mapping
  putStrLn "<< new type matcher"

  let substToVoid = map (\i -> (toType i, TCon "void" [])) (interfaces skin)
  return $ substSkin (mapping ++ substToVoid) skin


substSkin :: TypeMapping -> Skin -> Skin
substSkin s skin = skin { interfaces = substInterfaces s (interfaces skin),
                          factories = substCtors s (factories skin),
                          rules = substRules s (rules skin),
                          tokens = substTokens s (tokens skin),
                          templates = substTemplates s (templates skin) }
  where
    substTemplates s = map (substTemplate s)
    substTemplate s (Template t1 t2 rhs e) = Template (substType s t1) (substType s t2) rhs (substExp s e)

    substTokens s = map (substToken s)
    substToken s (x, t) = (x, substType s t)

    substInterfaces s = map (substInterface s)
    substInterface s (JInterface label super) = JInterface (substLabel s label) (substType s super)

    substCtors s = map (substCtor s)
    substCtor s (JConstructor label fields super) = JConstructor label (substFields s fields) (substType s super)

    substRules s = map (substRule s)
    substRule s (Rule typ label rhs e) = Rule (substType s typ) label rhs (substExp s e)

    substFields s = map (substField s)
    substField s (x,t) = (x, substType s t)

    substType s (TCon label ts) = TCon (substLabel s label) (map (substType s) ts)
    substType s (TVar x) = TVar x
    substType s TBoh = error $ "cannot type " ++ show TBoh

    substLabel [] label = label
    substLabel ((TCon old _, TCon new _):rest) label
      | label == old = new
      | otherwise    = substLabel rest label

    substExp s e = do
      let e' = substExp' s e
      case typeof e' of
        TCon "void" [] -> JK "()" (TCon "void" [])
        t              -> e'

    substExp' s (JNew es t)  = JNew (map (substExp s) es) (substType s t)
    -- substExp' s (JNew es t) = JNew (map (substExp s) es) t -- do not substitute classes
    substExp' s (JOp k es t) = JOp k (map (substExp s) es) (substType s t)
    substExp' s (JK k t)     = JK k (substType s t)
    substExp' s (JVar x t)   = JVar x (substType s t)

-- Remove all unused factories.
-- Remove any rule that calls a dead factory.
-- Remove any dead nonterminals from RHSs. If this causes a rule to become an epsilon rule, remove the rule.
-- Repeat...
removeUnreachableRules :: String -> Skin -> JAST -> [Rule]
removeUnreachableRules start skin jast = filter (`elem` covered) (rules skin)
  where
    covered = findCoveredRules skin (jconstructors jast)

    reachable = go (findRulesFor start (rules skin)) [start]

    actionUsed (Rule t lhs rhs action) = False

    -- remove any rules where the action calls a non matched factory
    -- remove any dead nonterminals from RHS
    -- remove any unusued nonterminals
    go frontier visited = rules

    findRulesFor lhs = filter (\(Rule _ x _ _) -> lhs == x)


data MatchResult = Match Int JConstructor JExp
                 | NoMatch JExp
  deriving Show

type Probability = Double
type TypeMapping = [(Type, Type)]

class ConvertToType a where
  toType :: a -> Type

instance ConvertToType JInterface where
  toType (JInterface label _) = TCon label []

instance ConvertToType JConstructor where
  toType (JConstructor label _ _) = TCon label []

-- generate a random mapping, then improve using the Metropolis algorithm
matchTypesMetropolis :: [Probability] -> Skin -> JAST -> TypeMapping
matchTypesMetropolis randoms skin jast = result
  where
    is :: [Type]
    is = map toType (interfaces skin) ++ map toType (factories skin)

    js :: [Type]
    js = map toType (jinterfaces jast)  ++ map toType (jconstructors jast)

    ihierarchy :: M.Map String Type
    ihierarchy = makeHierarchy (interfaces skin) (factories skin)

    jhierarchy :: M.Map String Type
    jhierarchy = makeHierarchy (jinterfaces jast) (jconstructors jast)

    result :: TypeMapping
    result = evalState findMapping randoms

    nextRandom :: State [Probability] Probability
    nextRandom = do
      randoms <- get
      put (tail randoms)
      return (head randoms)

    randomIndex :: Int -> State [Probability] Int
    randomIndex n = do
      j <- nextRandom
      let k = round $ j * fromIntegral n
      if k < 0 || k >= n
        then randomIndex n
        else return k

    -- Not the best shuffling algorithm, but works for our purposes.
    -- System.Random.Shuffle is obscure.
    shuffle :: [a] -> State [Probability] [a]
    shuffle xs = case xs of
      [] -> return []
      [x] -> return [x]
      xs -> do
        let n = length xs
        j <- randomIndex n
        as <- shuffle (drop j xs)
        bs <- shuffle (take j xs)
        return $ as ++ bs

    crossProduct :: [a] -> [b] -> [(a, b)]
    crossProduct = liftM2 (,)

    -- all possible mappings (including duplicates)
    universe :: TypeMapping
    universe = crossProduct is js

    -- generate a random mapping, but don't map an i to more than one j
    initialMapping :: State [Probability] TypeMapping
    initialMapping = do
      es <- filterM selectEdge universe
      es' <- shuffle es
      return $ removeDups es

    removeDups :: TypeMapping -> TypeMapping
    removeDups es = go es []
      where
        go [] acc = acc
        go ((i,j):rest) acc =
              go rest ((i,j):filter (\(i',j') -> i /= i') acc)

    findMapping :: State [Probability] TypeMapping
    findMapping = do
      ijs <- initialMapping
      iterateMapping numIterations ijs

    -- Metropolis algorithm parameters
    beta = fromIntegral $ length is + length js
    f ijs = exp $ fromIntegral (- beta * cost ijs)
    alpha ijs ijs' = min 1 (f ijs' / f ijs)
    edgeSelectionThreshold = min 0.7 (fromIntegral (length js) / fromIntegral (length is))
    numIterations = 30 * (length is + length js)

    iterateMapping :: Int -> TypeMapping -> State [Probability] TypeMapping
    iterateMapping iters ijs =
      if iters == 0
        then
          return ijs
        else do
          ijs' <- nextMapping ijs
          r <- nextRandom
          if r < alpha ijs ijs'
            then iterateMapping (iters-1) ijs'
            else iterateMapping (iters-1) ijs

    selectEdge :: (Type, Type) -> State [Probability] Bool
    selectEdge (i,j) = do
      r <- nextRandom
      return $ r < edgeSelectionThreshold

    cost :: [(Type, Type)] -> Int
    cost edges = sum (map subtypeViolationCost (crossProduct edges edges) ++ map siblingViolationCost (crossProduct edges edges) ++ map arityViolationCost edges ++ map renamingCost edges) + missingCost edges is js

    missingCost :: [(Type, Type)] -> [Type] -> [Type] -> Int
    missingCost edges is js = length is - length edges

    subtypeViolationCost :: ((Type, Type), (Type, Type)) -> Int
    subtypeViolationCost ((i,j), (i',j')) = length $ filter id [isSubtype ihierarchy i i' /= isSubtype jhierarchy j j',
                                                                isSubtype ihierarchy i' i /= isSubtype jhierarchy j' j]

    siblingViolationCost :: ((Type, Type), (Type, Type)) -> Int
    siblingViolationCost ((i,j), (i',j')) = if (supertype ihierarchy i == supertype ihierarchy i') /= (supertype jhierarchy j == supertype jhierarchy j')
                                              then 1
                                              else 0

    arityViolationCost :: (Type, Type) -> Int
    arityViolationCost (i, j) = 0

    renamingCost :: (Type, Type) -> Int
    renamingCost (TCon i [], TCon j []) = if i == j then 0 else matchName skin i j + matchName skin j i
    renamingCost (_, _) = 99999

    -- randomly delete some mappings
    nextMapping :: TypeMapping -> State [Probability] TypeMapping
    nextMapping mapping = do
      r <- nextRandom
      firstPart <- if r < 0.7
                    then do
                      k <- randomIndex (length mapping)
                      return $ take k mapping ++ drop (k+1) mapping
                    else
                      return mapping
      r <- nextRandom
      secondPart <- if r < 0.7
                      then do
                        es <- initialMapping
                        k <- randomIndex (length es)
                        return $ take 1 (drop k es)
                      else
                        return []
      return $ firstPart ++ removeDups secondPart

-- find all the covered rules
findCoveredRules :: Skin -> [JConstructor] -> [Rule]
findCoveredRules skin ks = filter (ruleInvokes ks) (rules skin)
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

data Variance = Covariant | Contravariant
  deriving (Show, Eq)

  -- find rules with similar types
  -- Method should map to "declaration"
  -- I think to make this work nicely, we need to loosen the types of the skin grammar
  -- to allow arbitrary declarations at any level.

-- Generate the RHS of a rule given the expression.
-- TODO: add parent type for generating template
generateRhs :: Maybe Type -> SubtypeEnv -> JExp -> State Skin [(Sym, String)]
generateRhs _ _ e | trace ("generateRhs for " ++ show e) False = undefined
generateRhs parent hierarchy (JNew es (TCon label [])) = do
  k <- makeKeyword label
  rhs <- mapM (generateRhs parent hierarchy) es
  return $ (Terminal k, "_") : concat rhs
generateRhs parent hierarchy (JOp label es t) = do
  k <- makeKeyword label
  rhs <- mapM (generateRhs parent hierarchy) es
  return $ (Terminal k, "_") : concat rhs
generateRhs parent hierarchy (JVar x t) = do
  lhs <- findSymbolForType parent Contravariant hierarchy t
  return [(lhs, x)]
generateRhs parent hierarchy (JK label t) = do
  k <- makeKeyword label
  return [(Terminal k, "_")]
generateRhs parent hierarchy e =
  error $ "missing case in generateRhs " ++ show e

makeKeyword :: String -> State Skin String
makeKeyword s = do
  let k = map toLower s
  modify (\skin -> skin { tokens = nub $ (k, TCon "void" []) : tokens skin })
  return k

findSymbolForType :: Maybe Type -> Variance -> SubtypeEnv -> Type -> State Skin Sym
findSymbolForType _ _ _ t | trace ("findSymbolForType for " ++ show t) False = undefined
findSymbolForType parent variance hierarchy t = do
  rs <- gets rules
  ts <- gets tokens
  let rulesWithRightType = filter (\(Rule rt _ _ _) -> isSubtype hierarchy rt t) rs
  let lhss = nub $ map (\(Rule _ lhs _ _) -> lhs) (trace (show rs) rulesWithRightType)
  let tokensWithRightType = nub $ filter (\(x, rt) -> isSubtype hierarchy rt t) ts
  let token = fmap fst (listToMaybe tokensWithRightType)
  case lhss of
    (lhs:_) -> return $ Nonterminal lhs
    [] -> case token of
      Just token -> return $ Terminal token
      Nothing    -> do
        -- templateMatches <- case parent of
        --   Nothing -> return []
        --   Just u -> do
        --     tms <- gets templates
        --     return $ filter (\(Template parentType childType rhs action) -> u == parentType && t == childType) tms
        let templateMatches = []
        case templateMatches of
          -- [Template _ _ rhs action] -> do
          --   let name = show t
          --   let rule = Rule t name rhs action
          --   modify (\skin -> skin { rules = rule : rules skin })
          --   return $ Nonterminal name
          _ ->
            case t of
              -- TCon "Object" [] -> return $ Terminal "IDENTIFIER"
              -- TODO: use the templates for these.
              TCon "String" [] -> return $ Terminal "IDENTIFIER"
              TCon "int" [] -> return $ Terminal "INT_LITERAL"
              TCon "Array" [a] -> do
                list <- findSymbolForType parent variance hierarchy (TCon "List" [a])
                let name = symname list ++ "_array"
                let rule = Rule t name [(list, "as")] (JOp "listToArray" [JVar "as" (TCon "List" [a])] t)
                modify (\skin -> skin { rules = rule : rules skin })
                return $ Nonterminal name
              TCon "List" [a] -> do
                token <- findSymbolForType parent variance hierarchy a
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
                modify (\skin -> skin { rules = [rule1, rule2, rule3, rule4] ++ rules skin })
                return $ Nonterminal name
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
      let rule = Rule (typeof e) lhs rhs e
      modify (\skin -> skin { rules = rule : rules skin })
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

  forM_ matchResults print

  -- For each unmatched constructor call, for each subexpression of the
  -- call, make sure there is a grammar rule for that subexpression's type.

  -- newRules <- forM [e | NoMatch e <- matchResults] $ generateRulesForSubexpressions

  -- For each unmatched constructor, generate a new factory method and generate a new rule that invokes that method.

  putStrLn "original rules (with types subst'ed)"
  forM_ (rules matchedSkin) print
  putStrLn "<< original rules (with types subst'ed)"

  -- Unlike when matching, include the constructors in the subtype hierarchy when generating new rules.
  let hierarchyWithConstructors = makeHierarchy (jinterfaces typedJast) (jconstructors typedJast)
  -- let hierarchyWithConstructors = M.insert "Method" (TCon "Declaration" []) hierarchy
  let skinWithNewRules = execState (makeNewRules matchResults hierarchyWithConstructors) matchedSkin

  putStrLn "new rules"
  forM_ (rules skinWithNewRules) print
  putStrLn "<< new rules"

  -- Need to prune the grammar.
  -- Starting at root symbol ("goal")
  -- eliminate rhs symbols that aren't covered by the factory calls

  let finalSkin = skinWithNewRules { rules = removeUnreachableRules "goal" skinWithNewRules typedJast }

  putStrLn "removed unreachable rules"
  forM_ (rules finalSkin) print
  putStrLn "<< removed unreachable rules"

  return ()
