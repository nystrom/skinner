module Typer (typeCheckSkin) where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

import Data.Char (isUpper, isLower)
import Data.Maybe (catMaybes, isNothing)
import Data.List ((\\))

import qualified Data.Map as M

import Debug.Trace (trace)

import Aliases
import AST

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

-- Notation:
-- TCon is a parser type constructor name
-- C is an AST type constructor name
-- tau, sigma are types
-- alpha, beta are type variables
--
-- TCon matches C ==> tau == sigma
-- tau == sigma
data Constraint = EqConstraint String Type Type | FailedConstraint String Constraint
        | AscribeConstraint String Type

instance Show Constraint where
  show (EqConstraint m t1 t2) = m ++ " -- " ++ show t1 ++ " == " ++ show t2
  show (FailedConstraint m c) = m ++ "! " ++ show c
  show (AscribeConstraint x t) = x ++ " :: " ++ show t

data TCRec = TCRec { nextTyvar :: Int, constraints :: [Constraint] }
  deriving Show

data Env = Env { tyenv :: M.Map String Type }
  deriving Show

type EnvT = ReaderT Env
type ConstraintsT = StateT TCRec

-- Mapping from type variables to types
type Subst = [(Tyvar, Type)]

merge :: Subst -> Subst -> Subst
merge s1 s2 = s1' ++ s2'
  where
    s1' = concatMap (\(x,t1) -> case lookup x s2 of { Just t2 -> mgu t1 t2 ; Nothing -> [(x,t1)] }) s1
    s2' = [(x,t) | (x,t) <- s2, isNothing (lookup x s1)]

    mgu (TCon a as) (TCon b bs) | a == b = concat $ zipWith mgu as bs
    mgu (TVar a) (TVar b) | a == b = []
    mgu (TVar a) (TVar b) | a < b  = [(a,TVar b)]
    mgu (TVar a) (TVar b) | b < a  = [(b,TVar a)]
    mgu (TVar a) t                 = [(a,t)]
    mgu t (TVar a)                 = [(a,t)]
    mgu t t'                       = error $ "cannot unify " ++ show t ++ " and " ++ show t'

-- Type checking monad
type TC = ConstraintsT (EnvT Identity)
-- type TC = ReaderT Env (StateT TCRec Identity)

lookupVar :: String -> TC Type
lookupVar x = do
  env <- ask
  return $ maybe (error $ "undefined variable " ++ x) id (M.lookup x (tyenv env))

-- add a bunch of bindings to the type environment
addBindings bindings env = env {
    tyenv = foldr (\(x, t) env -> M.insert x t env) (tyenv env) bindings
  }

rhsBindings rhs env =
  trace ("bindings for " ++ (show rhs) ++ " = " ++ (show $ map f rhs)) $
    addBindings (catMaybes $ map f rhs) env
  where
    f (Nonterminal sym, "_") = Nothing
    f (Terminal sym, "_") = Nothing
    f (Nonterminal sym, name) = fmap (\x -> (name,x)) $ M.lookup sym (tyenv env)
    f (Terminal sym, name) = fmap (\x -> (name,x)) $ M.lookup sym (tyenv env)

bind :: String -> Type -> TC a -> TC a
bind x t m =
    local (insertBinding x t) m
  where
    insertBinding x t env = env { tyenv = M.insert x t (tyenv env) }

freshTyvar :: TC Tyvar
freshTyvar = do
  rec <- get
  let next = nextTyvar rec
   in do
      put $ rec { nextTyvar = next+1 }
      return $ Tyvar ("_" ++ (show next))

addTyConstraint :: Constraint -> TC ()
addTyConstraint c = do
  rec <- get
  put $ rec { constraints = c : constraints rec }
  return ()

-- runTC :: [Constructor] -> TC a -> (a, [Constraint])
-- runTC :: Monad m => [Constructor] -> TC a -> m (a, TCRec)
runTC :: TC a -> (a, [Constraint])
runTC m = (x, constraints endState)
  where
    (x, endState) = runIdentity $ runReaderT (runStateT m st) env
    env = Env { tyenv = M.empty }
    st = TCRec { nextTyvar = 0, constraints = [] }

typeCheck :: Exp -> TC JExp
typeCheck (Op "++" [e1,e2]) = do
  a <- freshTyvar
  e1' <- typeCheck e1
  e2' <- typeCheck e2
  addTyConstraint (EqConstraint (show e1) (typeof e1') (TCon "List" [TVar a]))
  addTyConstraint (EqConstraint (show e2) (typeof e2') (TCon "List" [TVar a]))
  return (JOp "++" [e1', e2'] (typeof e2'))
typeCheck (Op ":" [e1,e2]) = do
  a <- freshTyvar
  e1' <- typeCheck e1
  e2' <- typeCheck e2
  addTyConstraint (EqConstraint (show e1) (typeof e1') (TVar a))
  addTyConstraint (EqConstraint (show e2) (typeof e2') (TCon "List" [TVar a]))
  return (JOp ":" [e1',e2'] (typeof e2'))
typeCheck (K "Nil" []) = do
  a <- freshTyvar
  return $ JK "Nil" (TCon "List" [TVar a])
typeCheck (K "Nothing" []) = do
  a <- freshTyvar
  return $ JK "Nothing" (TCon "Maybe" [TVar a])
typeCheck (K "Just" [e1]) = do
  a <- freshTyvar
  e1' <- typeCheck e1
  return $ JOp "Just" [e1'] (TCon "Maybe" [typeof e1'])
typeCheck (K "True" []) =
  return $ JK "True" (TCon "Boolean" [])
typeCheck (K "False" []) =
  return $ JK "False" (TCon "Boolean" [])
typeCheck (K "()" []) =
  return $ JK "()" (TCon "()" [])
typeCheck (K k []) = do
  t <- lookupVar k
  return $ JK k t
typeCheck (K k es) = do
  a <- freshTyvar
  es' <- mapM typeCheck es
  let ts = map typeof es'
  -- addTyConstraint (EqConstraint (show $ K k es) t (foldr funType (TVar a) ts))
  return $ JNew es' (TCon k [])
typeCheck (Var x) = do
  t <- lookupVar x
  return $ JVar x t
typeCheck e =
  error $ "missing case " ++ show e

typeCheckRules tokens factories rules = do
  bindings <- forM rules $ \(Rule t lhs rhs action) ->
    return (lhs, t)

  tokenBindings <- forM tokens $ \(name, t) ->
    return (name, t)

  typeBindings <- forM factories $ \(JConstructor label children super) ->
    return (label, funType' (map snd children) super)

  jrules <- local (addBindings $ typeBindings ++ bindings ++ tokenBindings) $
    forM rules $ \(Rule tlhs lhs rhs action) ->
      local (rhsBindings rhs) $ do
        e' <- typeCheck action
        addTyConstraint (EqConstraint lhs tlhs (typeof e'))
        return $ JRule tlhs lhs rhs e'

  rec <- get
  put $ rec { constraints = unify (constraints rec) ++ map (uncurry AscribeConstraint) bindings }

  rec <- get
  put $ rec { constraints = filter (not . useless) (constraints rec) }

  return jrules

typeCheckSkin :: Skin -> IO Skin
typeCheckSkin skin = do
  -- Type check the rules in the grammar rules
  let (jrules', _) = runTC $ typeCheckRules (tokens skin) (factories skin) (rules skin)
  return skin { jrules = jrules' }

useless :: Constraint -> Bool
useless (EqConstraint _ t1 t2)
  | t1 == t2 = True
  | otherwise = False
useless c = False

unify :: [Constraint] -> [Constraint]
unify (EqConstraint m (TVar (Tyvar x1)) t2:constraints) = unify $ map (substCon x1 t2) constraints
unify (EqConstraint m t2 (TVar (Tyvar x1)):constraints) = unify $ map (substCon x1 t2) constraints
unify (c @ (EqConstraint m (TCon k1 ts1) (TCon k2 ts2)):constraints)
  | k1 == k2 && length ts1 == length ts2 = unify $ zipWith (EqConstraint m) ts1 ts2 ++ constraints
  | otherwise = FailedConstraint ("cannot unify " ++ k1 ++ " and " ++ k2) c:unify constraints
unify (c:constraints) = c:unify constraints
unify [] = []

substCon :: String -> Type -> Constraint -> Constraint
substCon x t (EqConstraint m t1 t2) = EqConstraint m (subst x t t1) (subst x t t2)
substCon x t (AscribeConstraint x1 t1) = AscribeConstraint x1 (subst x t t1)

subst :: String -> Type -> Type -> Type
subst x t t' @ (TVar (Tyvar y))
  | x == y    = t
  | otherwise = t'
subst x t (TCon label ts) = TCon label (map (subst x t) ts)
