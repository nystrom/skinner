module Solver(SolverMonad, Node(..), Constraint(..), addTypeDistance, addConstructorDistance, addConstraint, solve, runSolver) where

import AST
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Control.Monad
import Control.Monad.State
import Numeric.LinearProgramming
import Data.List (nub, sort)
import Debug.Trace (trace)

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

type JType = Type

data Node = TypeNode Type
          | ConstructorNode JConstructor
          | JTypeNode JType
          | JConstructorNode JConstructor
  deriving (Eq,Ord)

instance Show Node where
  show (TypeNode t) = show t
  show (ConstructorNode (JConstructor label _ _)) = label
  show (JTypeNode t) = show t
  show (JConstructorNode (JConstructor c _ _)) = c

type SolverMonad a = State SolverState a

data SolverState = SolverState { constraints :: [Constraint],
                                 distances :: [(Node, Node, Int)] }
  deriving Show

data Constraint = OneOf [(Node, Node)] | Implies (Node, Node) (Node, Node)
  deriving Show

runSolver m = runState m (SolverState [] [])

addConstraint :: Constraint -> SolverMonad ()
addConstraint c = do
  trace ("addConstraint " ++ show c) $ return ()
  s <- get
  put $ s { constraints = c:constraints s }
  return ()

addTypeDistance :: Type -> JType -> Int -> SolverMonad ()
addTypeDistance x y n = do
  trace ("addTypeDistance " ++ show x ++ " " ++ show y ++ " " ++ show n) $ return ()
  s <- get
  put $ s { distances = (TypeNode x, JTypeNode y, n):distances s }
  return ()

addConstructorDistance :: JConstructor -> JConstructor -> Int -> SolverMonad ()
addConstructorDistance x y n = do
  trace ("addConstructorDistance " ++ show x ++ " " ++ show y ++ " " ++ show n) $ return ()
  s <- get
  put $ s { distances = (ConstructorNode x, JConstructorNode y, n):(distances s) }
  return ()

solve :: SolverMonad (Maybe [(Node,Node)])
solve = do
  s <- get

  let ds = nub $ sort $ distances s

  let keys = map (\(s, t, n) -> (s,t)) ds

  let nodeMap = Map.fromList (keys `zip` [1..])
  let revNodeMap = Map.fromList ([1..] `zip` keys)

  let dists = map (\(s, t, n) -> fromIntegral n) $ ds
  let top = maximum dists

  let problem = Maximize $ map (top-) dists

  let pos s =   1  # (case Map.lookup s nodeMap of
                                Just x -> x
                                Nothing -> error $ "pos: not found " ++ show s)
  let neg s = (-1) # (case Map.lookup s nodeMap of
                                Just x -> x
                                Nothing -> error $ "neg: not found " ++ show s)

  -- Lambda 2 synthesizer: bitbucket.org/jfeser/l2
  -- works with input-output pairs

  let c1 = map (\k -> [ pos k ] :<=: 1) keys
  let c2 = map (\c -> case c of
              OneOf ss -> (map pos ss) :<=: 1
              Implies s t -> [ pos s, neg t ] :<=: 0) $ constraints s

  let sparse = Sparse $ c1 ++ c2

  let soln = simplex problem sparse []

  case soln of
    Optimal (cost, coeffs) ->
      let summarize (alpha, (s, t, dist)) =
            if (floor alpha) == 0
              then []
              else [(s, t)]
          result = concatMap summarize (coeffs `zip` ds)
        in return $ Just result
    Infeasible (cost, coeffs) ->
      let summarize (alpha, (s, t, dist)) =
            if (floor alpha) == 0
              then []
              else [(s, t)]
          result = concatMap summarize (coeffs `zip` ds)
        in return $ Just result
    Feasible (cost, coeffs) ->
      let summarize (alpha, (s, t, dist)) =
            if (floor alpha) == 0
              then []
              else [(s, t)]
          result = concatMap summarize (coeffs `zip` ds)
        in return $ Just result
    NoFeasible ->
      trace ("soln = " ++ show soln ++ "\nstate " ++ show s) return Nothing
    Undefined ->
      trace ("soln = " ++ show soln ++ "\nstate " ++ show s) return Nothing
    Unbounded ->
      trace ("soln = " ++ show soln ++ "\nstate " ++ show s) return Nothing
