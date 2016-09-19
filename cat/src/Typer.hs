module Typer (typeCheckSkin, makeHierarchy) where

import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State

import           Control.Applicative    ((<$>))
import           Data.Char              (isLower, isUpper)
import           Data.List              (intersect, (\\))
import           Data.Maybe             (catMaybes, fromMaybe, isNothing,
                                         mapMaybe)

import qualified Data.Map               as M

import           Debug.Trace            (trace)

import           Aliases
import           AST

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

data TCRec = TCRec { nextTyvar :: Int, currSubst :: Subst }
  deriving Show

data Env = Env { tyenv :: M.Map String Type, supers :: M.Map String Type }
  deriving Show

type EnvT = ReaderT Env
type ConstraintsT = StateT TCRec

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

mgu :: M.Map String Type -> Type -> Type -> Subst
mgu h t1 t2 = go t1 t2
  where
    go (TVar a) (TVar b) | a == b = []
    go (TVar a) (TVar b) | a < b  = [(a,TVar b)]
    go (TVar a) (TVar b) | b < a  = [(b,TVar a)]
    go (TVar a) t                 = [(a,t)]
    go t (TVar a)                 = [(a,t)]
    go (TCon "->" [s1,t1]) (TCon "->" [s2,t2]) = go s2 s1 ++ go t1 t2           -- handle contravariant function arguments
    go (TCon a as) (TCon b bs) | a == b = concat $ zipWith go as bs             -- other type constructors are covariant
    go (TCon a []) (TCon b []) = trace ("go " ++ a ++ " ~ " ++ b) $ case M.lookup a h of
                                    Just (TCon s []) -> go (TCon s []) (TCon b [])
                                    Nothing ->
                                      error $ "cannot unify " ++ show (TCon a []) ++ " and " ++ show (TCon b []) ++ " on behalf of " ++ show t1 ++ " and " ++ show t2
    go t1' t2' =
      error $ "cannot unify " ++ show t1' ++ " and " ++ show t2' ++ " on behalf of " ++ show t1 ++ " and " ++ show t2

-- Type checking monad
type TC = ConstraintsT (EnvT Identity)
-- type TC = ReaderT Env (StateT TCRec Identity)

lookupVar :: String -> TC Type
lookupVar x = do
  env <- ask
  return $ fromMaybe (error $ "undefined variable " ++ x) (M.lookup x (tyenv env))

-- add a bunch of bindings to the type environment
addBindings bindings env = env {
    tyenv = foldr (\(x, t) env -> M.insert x t env) (tyenv env) bindings
  }

rhsBindings rhs env =
  -- trace ("bindings for " ++ show rhs ++ " = " ++ show (map f rhs)) $
    addBindings (mapMaybe f rhs) env
  where
    f (Nonterminal sym, "_")  = Nothing
    f (Terminal sym, "_")     = Nothing
    f (Nonterminal sym, name) = (\x -> (name, x)) <$> M.lookup sym (tyenv env)
    f (Terminal sym, name)    = (\x -> (name, x)) <$> M.lookup sym (tyenv env)

bind :: String -> Type -> TC a -> TC a
bind x t =
    local (insertBinding x t)
  where
    insertBinding x t env = env { tyenv = M.insert x t (tyenv env) }

freshTyvar :: TC Tyvar
freshTyvar = do
  rec <- get
  let next = nextTyvar rec
   in do
      put $ rec { nextTyvar = next+1 }
      return $ Tyvar ("_" ++ show next)

-- runTC :: [Constructor] -> TC a -> (a, [Constraint])
-- runTC :: Monad m => [Constructor] -> TC a -> m (a, TCRec)
runTC :: M.Map String Type -> TC a -> a
runTC subtypeHierarchy m = x
  where
    (x, endState) = runIdentity $ runReaderT (runStateT m st) env
    env = Env { tyenv = M.empty, supers = subtypeHierarchy }
    st = TCRec { nextTyvar = 0, currSubst = emptySubst }

emptySubst :: Subst
emptySubst = []

-- Unify, but allow the first type to be a subtype of the second.
unifySubtype :: Type -> Type -> TC ()
unifySubtype t1 t2 = do
  rec <- get
  h <- asks supers
  let s = currSubst rec
  let s' = mgu h t1 t2
  put $ rec { currSubst = merge s' s }

subst :: Subst -> JExp -> JExp
subst s (JNew es t) = do
  let es' = map (subst s) es
  JNew es' (substTy s t)
subst s (JOp k es t) = do
  let es' = map (subst s) es
  JOp k es' (substTy s t)
subst s (JK k t) =
  JK k (substTy s t)
subst s (JVar x t) =
  JVar x (substTy s t)

typeCheck :: JExp -> TC JExp
typeCheck (JOp "++" [e1, e2] _) = do
  e1' <- typeCheck e1
  e2' <- typeCheck e2
  a <- freshTyvar
  unifySubtype (typeof e1') (TCon "List" [TVar a])
  unifySubtype (typeof e2') (TCon "List" [TVar a])
  return (JOp "++" [e1', e2'] (TCon "List" [TVar a]))
typeCheck (JOp ":" [e1, e2] _) = do
  e1' <- typeCheck e1
  e2' <- typeCheck e2
  a <- freshTyvar
  unifySubtype (typeof e1') (TVar a)
  unifySubtype (typeof e2') (TCon "List" [TVar a])
  return (JOp ":" [e1', e2'] (TCon "List" [TVar a]))
typeCheck (JK "Nil" _) = do
  a <- freshTyvar
  return $ JK "Nil" (TCon "List" [TVar a])
typeCheck (JK "Nothing" _) = do
  a <- freshTyvar
  return $ JK "Nothing" (TCon "Maybe" [TVar a])
typeCheck (JOp "Just" [e1] _) = do
  e1' <- typeCheck e1
  return $ JOp "Just" [e1'] (TCon "Maybe" [typeof e1'])
typeCheck (JK "true" _) =
  return $ JK "true" (TCon "boolean" [])
typeCheck (JK "false" _) =
  return $ JK "false" (TCon "boolean" [])
typeCheck (JK "()" _) =
  return $ JK "()" (TCon "void" [])
typeCheck (JK k _) = do
  t <- lookupVar k
  return $ JK k t
typeCheck (JNew es (TCon k [])) = do
  es' <- mapM typeCheck es
  let ts = map typeof es'
  TCon "->" [ts', t'] <- lookupVar k
  unifySubtype (tupleType ts) ts'
  unifySubtype t' (TCon k [])
  unifySubtype (TCon k []) t'
  -- t' <- lookupVar k
  -- unifySubtype (funType' ts (TCon k [])) t'
  return $ JNew es' (TCon k [])
typeCheck (JOp k es _) = do
  es' <- mapM typeCheck es
  let ts = map typeof es'
  TCon "->" [ts', t'] <- lookupVar k
  unifySubtype (tupleType ts) ts'
  -- unifySubtype t' (TCon k [])
  -- unifySubtype (TCon k []) t'
  -- t' <- lookupVar k
  -- unifySubtype (funType' ts (TCon k [])) t'
  return $ JOp k es' t'
typeCheck (JVar x _) = do
  t <- lookupVar x
  case t of
    TBoh -> error $ "type of " ++ x ++ " in environment was " ++ show t
    _    -> return ()
  return $ JVar x t
typeCheck e =
  error $ "missing case " ++ show e

typeCheckRules tokens factories rules templates = do
  bindings <- forM rules $ \(Rule t lhs rhs action) ->
    return (lhs, t)

  tokenBindings <- forM tokens $ \(name, t) ->
    return (name, t)

  typeBindings <- forM factories $ \(JConstructor label children super) ->
    return (label, funType' (map snd children) super)

  let env = addBindings $ typeBindings ++ bindings ++ tokenBindings

  rules' <- local env $
    forM rules $ \(Rule tlhs lhs rhs action) ->
      local (rhsBindings rhs) $ do
        e' <- typeCheck action
        unifySubtype (typeof e') tlhs
        case typeof e' of
          TBoh -> error $ "could not replace type of " ++ show action ++ " with " ++ show e' ++ " in " ++ show (Rule tlhs lhs rhs action)
          _ -> return ()
        s <- gets currSubst
        return $ Rule (substTy s tlhs) lhs rhs (subst s e')

  templates' <- local env $
    forM templates $ \(Template told tlhs rhs action) ->
      local (rhsBindings rhs) $ do
        e' <- typeCheck action
        unifySubtype (typeof e') tlhs
        case typeof e' of
          TBoh -> error $ "could not replace type of " ++ show action ++ " with " ++ show e' ++ " in " ++ show (Template told tlhs rhs action)
          _ -> return ()
        s <- gets currSubst
        return $ Template (substTy s told) (substTy s tlhs) rhs (subst s e')

  return (rules', templates')

makeHierarchy :: [JInterface] -> [JConstructor] -> M.Map String Type
makeHierarchy is fs = h
  where
    h0 = M.empty
    h1 = foldl (\m (JInterface label super) -> M.insert label super m) h0 is
    h2 = foldl (\m (JConstructor label _ super) -> if super /= TCon label [] then M.insert label super m else m) h1 fs
    -- h2 = h1
    h3 = M.insert "String" (TCon "Object" []) h2
    h = h3

typeCheckSkin :: Skin -> IO Skin
typeCheckSkin skin = do
  -- Type check the rules in the grammar rules
  let subtypeHierarchy = makeHierarchy (interfaces skin) [] -- (factories skin)
  let (rules', templates') = runTC subtypeHierarchy $ typeCheckRules (tokens skin) (factories skin) (rules skin) (templates skin)
  return skin { rules = rules', templates = templates' }

substTy :: Subst -> Type -> Type
substTy s t @ (TVar x)    = fromMaybe t (lookup x s)
substTy s (TCon label ts) = TCon label (map (substTy s) ts)
substTy s TBoh            = TBoh
