module TreeMatch3 (match) where

import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Set as Set
import Data.Set ((\\))
import qualified Data.Map as Map
import Debug.Trace (trace)

import AST
import Aliases
import Solver

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

-- TODO: result should include rewritten actions !!!
type Result = (Int, [(JConstructor, JConstructor)], [(Type, Type)])

match :: [Aliases] -> [JConstructor] -> [JConstructor] -> Result
match aliases skinConstructors javaConstructors = fst $ runSolver matchAll
  where
    matchAll :: SolverMonad Result
    matchAll = do

      {-
       - PREPROCESSING:
       -
       - Generate new skinConstructors from existing skinConstructors as follows:
       - if there is a Java enum that matches many of the skinConstructor names
       - find the javaConstructor that takes the enum as a parameter (say Unary)
       - for each skinConstructor of the form, k [Exp], generate Unary [k, Exp]
       - Similarly for binary, literals, etc.
       - REWRITE actions to use new interface :-)
       -
       - Identify literals
       -
       - If there are factories of the form
       - K [Maybe A, B] extends A
       - K [B, Maybe A] extends A
       - Generate
       - K [List B] extends A
       -}



      let pairs = liftM2 (,) skinConstructors javaConstructors
      let pairs'' = filter (\(JConstructor _ skinFields _, javaCtor) -> case javaCtor of
                                 JConstructor _ javaFields _ -> length javaFields == length skinFields
                                 ) pairs
      let pairs' = map (\(a,b) -> (ConstructorNode a, JConstructorNode b)) pairs''

      forM_ pairs'' $ \(skinCtor, javaCtor) -> do
        match1 skinCtor javaCtor

      forM_ skinConstructors $ \skinCtor -> do
        let ps = filter (\(a,b) -> ConstructorNode skinCtor == a) pairs'
        addConstraint $ OneOf ps

      forM_ javaConstructors $ \javaCtor -> do
        let ps = filter (\(a,b) -> JConstructorNode javaCtor == b) pairs'
        addConstraint $ OneOf ps

      -- TODO: add constraint OneOf for types

      result <- solve

      debug "RESULT"
      debug (show result)

      case result of
        Just result -> do
          let f (TypeNode t, JTypeNode t') = []
              f (ConstructorNode k, JConstructorNode k') = [(k',k)]
          let g (TypeNode t, JTypeNode t') = [(t',t)]
              g (ConstructorNode k, JConstructorNode k') = []
          return $ (1, concatMap f result, concatMap g result)
        Nothing ->
          return $ (-1, [], [])

    match1 :: JConstructor -> JConstructor -> SolverMonad ()
    match1 skinCtor @ (JConstructor skinClassName skinFields _)
           javaCtor @ (JConstructor javaClassName javaFields _) = do
      matchArgs $ (map snd skinFields) `zip` (map snd javaFields)
      matchConstructor skinCtor javaCtor
      forM_ ((map snd skinFields) `zip` (map snd javaFields)) $ \(skinType, javaType) ->
        addConstraint $ Implies (ConstructorNode skinCtor, JConstructorNode javaCtor) (TypeNode skinType, JTypeNode javaType)

    matchConstructor :: JConstructor -> JConstructor -> SolverMonad ()
    matchConstructor skinCtor @ (JConstructor skinClassName skinFields _)
                     javaCtor @ (JConstructor javaClassName javaFields _) = do
      let dist = matchLabel javaClassName skinClassName
      addConstructorDistance skinCtor javaCtor dist

    matchArgs :: [(Type, Type)] -> SolverMonad ()
    matchArgs [] = return ()
    matchArgs ((t,jt):rest) = do
      matchArg1 t jt
      matchArgs rest

    matchArg1 :: Type -> Type -> SolverMonad ()
    matchArg1 skinType @ (TCon label _) javaType = do
      let dist = matchTypeToLabel javaType label
      addTypeDistance skinType javaType dist

    matchTypeToLabel (TCon "Array" [t]) label = matchTypeToLabel t label
    matchTypeToLabel (TCon "List" [t]) label = matchTypeToLabel t label
    matchTypeToLabel (TCon "Maybe" [t]) label = matchTypeToLabel t label
    matchTypeToLabel (TCon x ts) label = matchLabel x label
    matchTypeToLabel t label = matchLabel (show t) label

    matchLabel = matchNameWithAliases aliases