module Main (main) where

import Data.Monoid
import Control.Applicative((<$>), (<*>), (<*), (*>), (<$))
import Control.Monad.State
import Control.Monad.Reader
import System.Environment (getArgs)
import Data.List ((\\), find, sortBy, sortOn, minimum, minimumBy, nub)
import Data.List (intercalate)
import Data.Char (toLower, toUpper, isLower, isUpper)
import Data.Maybe (catMaybes, listToMaybe)
import Debug.Trace (trace)
import Text.Parsec (parse)

import Aliases
import AST
import JASTParse
import SkinParse
import Typer
-- import TreeMatch3
-- import Synth

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

typeof :: JExp -> Type
typeof (JNew es t) = t
typeof (JOp op es t) = t
typeof (JK k t) = t
typeof (JVar x t) = t

freeVars :: JExp -> [(String, Type)]
freeVars (JNew es t) = nub $ concatMap freeVars es
freeVars (JOp op es t) = nub $ concatMap freeVars es
freeVars (JK k t) = []
freeVars (JVar x t) = [(x, t)]

class Wordy a where
  toBagOfWords :: a -> [String]

instance Wordy JExp where
  toBagOfWords (JNew es t) = toBagOfWords t ++ concatMap toBagOfWords es
  toBagOfWords (JOp op es t) = toBagOfWords t
  toBagOfWords (JK k t) = k : toBagOfWords t
  toBagOfWords (JVar x t) = toBagOfWords t    -- NOTE: do not include the variable name

instance Wordy Type where
  toBagOfWords (TCon label []) = [label]
  toBagOfWords _ = []

isNullable :: Type -> Bool
isNullable = not . isPrimitive

isPrimitiveNumber :: Type -> Bool
isPrimitiveNumber (TCon "byte" []) = True
isPrimitiveNumber (TCon "short" []) = True
isPrimitiveNumber (TCon "char" []) = True
isPrimitiveNumber (TCon "int" []) = True
isPrimitiveNumber (TCon "long" []) = True
isPrimitiveNumber (TCon "float" []) = True
isPrimitiveNumber (TCon "double" []) = True
isPrimitiveNumber t = False

isPrimitive :: Type -> Bool
isPrimitive (TCon "void" []) = True
isPrimitive (TCon "boolean" []) = True
isPrimitive t = isPrimitiveNumber t

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

    -- t -> List[t]
    go s (TCon "List" [w]) | s == w = Just $ JOp "mkList1" [e] t
    -- List[t] -> Array[t]
    go (TCon "List" [u]) (TCon "Array" [w]) | u == w = Just $ JOp "listToArray" [e] t
    -- Array[t] -> List[t]
    go (TCon "Array" [u]) (TCon "List" [w]) | u == w = Just $ JOp "arrayToList" [e] t
    -- Maybe[t] -> List[t]
    go (TCon "Maybe" [u]) (TCon "List" [w]) | u == w = Just $ JOp "maybeToList" [e] t
    -- Maybe[t] -> t
    go (TCon "Maybe" [u]) t | u == t && isNullable t = Just $ JOp "unMaybe" [e] t
    -- t -> Maybe[t]
    go s (TCon "Maybe" [w]) | s == w = Just $ JOp "mkMaybe" [e] t

    -- (t,t) -> [t]
    go (TCon label [u, v]) (TCon "List" [w]) | u == w && v == w = Just $ JOp "mkList2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t,t) -> [t]
    go (TCon label [u, v, w]) (TCon "List" [x]) | u == x && v == x && w == x = Just $ JOp "mkList2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t) -> [t]
    go (TCon label [u, v]) (TCon "Array" [w]) | u == w && v == w = Just $ JOp "mkArray2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
    -- (t,t,t) -> [t]
    go (TCon label [u, v, w]) (TCon "Array" [x]) | u == x && v == x && w == x = Just $ JOp "mkArray2" [JOp (label ++ ".1") [e] u, JOp (label ++ ".2") [e] v] t
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
                              Just e -> coerce hierarchy e t
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
substVars s (JNew es t) = JNew (map (substVars s) es) t
substVars s (JOp k es t) = JOp k (map (substVars s) es) t
substVars s (JK k t) = JK k t
substVars s (JVar x t) = case lookup x s of
                          Just e -> e
                          Nothing -> JVar x t

-- Find the free variables of the expression.
-- Find a factory method with matching arguments and matching name.
matchConstructors :: JExp -> Reader (Skin, SubtypeEnv) MatchResult
matchConstructors (new @ (JNew args typ @ (TCon label []))) = do
  debug $ "match constructors vs " ++ show new

  (skin, hierarchy) <- ask

  let fv = freeVars new

  rs <- forM (factories skin) $ \k @ (JConstructor skinLabel skinFields skinSuper) -> do

    theta <- do -- trace ("matching " ++ show k ++ " with " ++ show new) $ do
      case (skinFields, fv) of
        -- HACK: if there are more parameter to the factory than there are free variables in
        -- the constructor call, try to tuple up the parameters
        ([(y1, t1'), (y2, t2')], [(x, TCon "List" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "mkList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) (TCon "List" [t]) of
            Just e -> return $ [(x, e)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, TCon "Array" [t])]) | t1' == t2' ->
          case coerce hierarchy (JOp "mkArray2" [JVar y1 t1', JVar y2 t1'] (TCon "Array" [t1'])) (TCon "Array" [t]) of
            Just e -> return $ [(x, e)]
            Nothing -> return []
        ([(y1, t1'), (y2, t2')], [(x, t)]) | t1' == t2' ->
          case coerce hierarchy (JOp "mkList2" [JVar y1 t1', JVar y2 t1'] (TCon "List" [t1'])) t of
            Just e -> return $ [(x, e)]
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
              Just e -> return $ Just (x, e)
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
    _ -> return $ NoMatch new

matchConstructors e = return $ NoMatch e


type SubtypeEnv = [(Type, Type)]

supertype :: SubtypeEnv -> Type -> Maybe Type
supertype env (TVar x) = Nothing
supertype env (TCon "Object" []) = Nothing
supertype env t = lookup t env

subtype :: SubtypeEnv -> Type -> Type -> Bool
subtype env t1 (TCon "Object" []) = True
subtype env t1 t2 | t1 == t2 = True
subtype env t1 t2 = case supertype env t1 of
                   Nothing -> False
                   Just t -> subtype env t t2

generateHierarchy :: JAST -> SubtypeEnv
generateHierarchy jast = []

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
        go [] ess = removeEnumVars ess
        go (e:rest) ess = go rest (addEnum e ess)

        removeEnumVars ess = filter (not . hasEnumVars) ess
        hasEnumVars es = any isEnumVar es
        isEnumVar ex = any (\e -> isThisEnumVar e ex) (jenums jast)
        isThisEnumVar (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = True
        isThisEnumVar _ _ = False

        addEnum :: JEnum -> [[JExp]] -> [[JExp]]
        addEnum e ess = concatMap (addEnum1 e) ess

        addEnum1 :: JEnum -> [JExp] -> [[JExp]]
        addEnum1 e es = nub $ (map (addEnum2 e) es) : es : []

        addEnum2 :: JEnum -> JExp -> JExp
        addEnum2 (JEnum enum (TCon esuper [])) (JVar x (TCon label [])) | esuper == label = JK enum (TCon label [])
        addEnum2 _ ex = ex

matchName :: Skin -> String -> String -> Int
matchName skin = matchNameWithAliases (aliases skin)

-- match types in the skin to types in the JAST, rewriting the skin
-- FIXME: currently this works by matching names using only aliases with no forgiveness
-- Also, it maps more than one skin type to the same JAST type, which may be broken
matchTypes :: Monad m => Skin -> JAST -> m Skin
matchTypes skin jast = do
  debug $ "match types"
  let is = interfaces skin
  let js = jinterfaces jast
  let match2 (j @ (JInterface label _)) (i @ (JInterface skinLabel _)) =
         let cost = matchName skin skinLabel label
           in (cost, i, j)
  let ks = filter (\(cost, _, _) -> cost <= 0) $ liftM2 match2 js is
  debug $ show $ take 10 $ sortOn (\(a,b,c) -> a) ks
  return $ substSkin (map (\(cost, j, i) -> (j, i)) ks) skin

  where
    substSkin s skin = skin { interfaces = substInterfaces s (interfaces skin), factories = substCtors s (factories skin), rules = substRules s (rules skin) }

    substInterfaces s js = map (substInterface s) js
    substInterface s (JInterface label super) = JInterface (substLabel s label) (substType s super)

    substCtors s js = map (substCtor s) js
    substCtor s (JConstructor label fields super) = JConstructor label (substFields s fields) (substType s super)

    substRules s js = map (substRule s) js
    substRule s (Rule typ label rhs e) = Rule (substType s typ) label rhs e

    substFields s fields = map (substField s) fields
    substField s (x,t) = (x, substType s t)

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

-- Find the rules that invoke the given constructors
findRules :: Skin -> [JConstructor] -> [Rule]
findRules skin k = []

-- Find an appropriate LHS for the given expression.
findAppropriateLhs :: Skin -> JExp -> String
findAppropriateLhs skin e = "expression"

  -- find rules with similar types
  -- Method should map to "declaration"
  -- I think to make this work nicely, we need to loosen the types of the skin grammar
  -- to allow arbitrary declarations at any level.

-- Generate the RHS of a rule given the expression.
generateRhs :: SubtypeEnv -> Skin -> JExp -> [(Sym, String)]
generateRhs hierarchy skin (JNew es (TCon label [])) = [(Terminal (keyword label), "_")] ++ concatMap (generateRhs hierarchy skin) es
generateRhs hierarchy skin (JVar x t) = [(findLhsForType hierarchy skin t, x)]

keyword :: String -> String
keyword s = map toLower s

findLhsForType :: SubtypeEnv -> Skin -> Type -> Sym
findLhsForType hierarchy skin t =
    trace ("finding lhs for " ++ show t) $
    case lhss of
      (lhs:_) -> Nonterminal lhs
      [] -> case token of
        Just token -> Terminal token
        Nothing -> Nonterminal ("A[" ++ show t ++ "]")
  where
    rulesWithRightType = filter (\(Rule rt _ _ _) -> subtype hierarchy rt t) (rules skin)
    lhss = nub $ map (\(Rule _ lhs _ _) -> lhs) rulesWithRightType
    tokensWithRightType = nub $ filter (\(x, rt) -> subtype hierarchy rt t) (tokens skin)
    token = fmap fst (listToMaybe tokensWithRightType)

translateAction :: Exp -> Type -> JExp
translateAction Unit (TCon "void" []) = JK "{}" (TCon "void" [])
translateAction (Var x) t = JVar x t
translateAction (K k) t = JK k t
translateAction (Op "Nothing") t = JK "null" t
translateAction (Op "Nil") (TCon "List" [t]) = JK ("Collections.emptyList<" ++ (show t) ++ ">()") (TCon "List" [t])
translateAction (Op "Nil") (TCon "Array" [t]) = JK ("new " ++ show t ++ "[0]") (TCon "Array" [t])
translateAction (Op "Zero") (TCon "int" []) = JK "0" (TCon "int" [])
translateAction (Op "Zero") (TCon "long" []) = JK "0L" (TCon "long" [])
translateAction (Op "True") (TCon "boolean" []) = JK "true" (TCon "boolean" [])
translateAction (Op "False") (TCon "boolean" []) = JK "false" (TCon "boolean" [])
translateAction (App (App (Op ":") e1) (App (App (Op ":") e2) (Op "Nil"))) (TCon "List" [t]) = JOp "mkList2" [translateAction e1 t, translateAction e2 t] (TCon "List" [t])
translateAction e t = error $ "missing synth " ++ show e ++ " :: " ++ show t

main :: IO ()
main = do
  -- Parse arguments
  args <- getArgs
  let skinFile = head args
  let astFile = head (tail args)

  -- read the skin and the java AST files
  skinput <- readFile $ skinFile
  jinput <- readFile $ astFile

  -- parse the skin
  case parse skin skinFile skinput of
    Left err ->
      debug $ "unparsable skin: " ++ show err
    Right skin -> do
      debug $ "skin: " ++ show skin

      -- parse the java AST file
      case parse javaAST "ast" jinput of
        Left err ->
          debug $ "unparsable java AST description: " ++ show err
        Right jast -> do
          debug $ "Java AST:\n" ++ show jast

          typeCheckSkin skin

          -- rename the types to match the JAST
          skin' <- matchTypes skin jast
          debug $ "skin': " ++ show skin'

          -- Type-check again.. This is just a sanity check that matchTypes didn't mess up the types
          typeCheckSkin skin'

          let hierarchy = generateHierarchy jast ++ generateSkinHierarchy skin'

          let jcalls = generateFactoryCalls jast
          debug $ "jcalls:\n" ++ intercalate "\n" (map show jcalls)

          debug $ "Matching AST with skin:"
          matchResults <- forM jcalls $ \k -> case k of
            JNew args t -> do
              return $ runReader (matchConstructors k) (skin', hierarchy)
            _ ->
              return $ NoMatch k

          forM matchResults $ putStrLn . show

          -- For each unmatched constructor call, for each subexpression of the
          -- call, make sure there is a grammar rule for that subexpression's type.

          -- newRules <- forM [e | NoMatch e <- matchResults] $ generateRulesForSubexpressions


          -- For each matched factory method, generate a JRule that invokes the factory method.
          -- Generate a JRule that invokes the factory method.

          let matchedRules = findRules skin [k | Match _ k e <- matchResults]

          -- For each unmatched constructor, generate a new factory method and generate a new rule that invokes that method.

          newRules <- forM matchResults $ \r -> case r of
            NoMatch e -> do
              let lhs = findAppropriateLhs skin' e
              let rhs = generateRhs hierarchy skin' e
              let rule = JRule (typeof e) lhs rhs e
              return $ Just rule
            _ -> return Nothing

          forM matchedRules $ putStrLn . show
          forM (catMaybes newRules) $ putStrLn . show

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

          debug $ "new grammar"

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
