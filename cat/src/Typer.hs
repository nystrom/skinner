module Typer (typeCheckSkin) where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

import Data.Char (isUpper, isLower)
import Data.Maybe (catMaybes)
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
runTC :: TC a -> [Constraint]
runTC m = constraints endState
  where
    (_, endState) = runIdentity $ runReaderT (runStateT m st) env
    env = Env { tyenv = M.empty }
    st = TCRec { nextTyvar = 0, constraints = [] }

typeCheck :: Exp -> TC Type
typeCheck (Op "++") = do
  a <- freshTyvar
  return $ funType (TCon "List" [TVar a]) (funType (TCon "List" [TVar a])
                                                  (TCon "List" [TVar a]))
typeCheck (Op ":") = do
  a <- freshTyvar
  return $ funType (TVar a) (funType (TCon "List" [TVar a]) (TCon "List" [TVar a]))
typeCheck (Op "Nil") = do
  a <- freshTyvar
  return $ TCon "List" [TVar a]
typeCheck (Op "Nothing") = do
  a <- freshTyvar
  return $ TCon "Maybe" [TVar a]
typeCheck (Op "Just") = do
  a <- freshTyvar
  return $ funType (TVar a) (TCon "Maybe" [TVar a])
typeCheck (Op "True") = do
  return $ TCon "Boolean" []
typeCheck (Op "False") = do
  return $ TCon "Boolean" []
typeCheck (Op "Zero") = do
  return $ TCon "Nat" []
typeCheck (Op "Succ") = do
  return $ funType (TCon "Nat" []) (TCon "Nat" [])
typeCheck Unit = do
  return $ TCon "()" []
typeCheck (App e1 e2) = do
  a <- freshTyvar
  t1 <- typeCheck e1
  t2 <- typeCheck e2
  addTyConstraint (EqConstraint (show $ App e1 e2) t1 (funType t2 (TVar a)))
  return $ TVar a
typeCheck (K k) = do
  lookupVar k
typeCheck (Var x) = do
  lookupVar x
typeCheck e = do
  trace ("missing case " ++ (show e)) return ()
  a <- freshTyvar
  return $ TVar a

typeCheckRules tokens factories rules = do
  bindings <- forM rules $ \(Rule t lhs rhs action) -> do
    return (lhs, t)

  tokenBindings <- forM tokens $ \(name, t) -> do
    return (name, t)

  typeBindings <- forM factories $ \(JConstructor label children super) -> do
    return (label, funType' (map snd children) super)

  local (addBindings $ typeBindings ++ bindings ++ tokenBindings) $
    forM_ rules $ \(Rule tlhs lhs rhs action) -> do
      local (rhsBindings rhs) $ do
        t <- typeCheck action
        addTyConstraint (EqConstraint lhs tlhs t)
        return ()

  rec <- get
  put $ rec { constraints = unify (constraints rec) ++ map (\(x,t) -> AscribeConstraint x t) bindings }

  rec <- get
  put $ rec { constraints = filter (not . useless) (constraints rec) }

  return ()

typeCheckSkin :: Skin -> IO ()
typeCheckSkin skin = do
  -- Type check the rules in the grammar rules
  let _ = runTC $ typeCheckRules (tokens skin) (factories skin) (rules skin)
  return ()

useless :: Constraint -> Bool
useless (EqConstraint _ t1 t2)
  | t1 == t2 = True
  | otherwise = False
useless c = False

unify :: [Constraint] -> [Constraint]
unify (EqConstraint m (TVar (Tyvar x1)) t2:constraints) = unify $ map (substCon x1 t2) constraints
unify (EqConstraint m t2 (TVar (Tyvar x1)):constraints) = unify $ map (substCon x1 t2) constraints
unify (c @ (EqConstraint m (TCon k1 ts1) (TCon k2 ts2)):constraints)
  | k1 == k2 && length ts1 == length ts2 = unify $ zipWith (\t1 t2 -> EqConstraint m t1 t2) ts1 ts2 ++ constraints
  | otherwise = (FailedConstraint ("cannot unify " ++ k1 ++ " and " ++ k2) c):unify constraints
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