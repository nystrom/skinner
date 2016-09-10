module Synth (synthFromModel) where

import Control.Monad (zipWithM)

import AST

type JType = Type
type ModelMap = [(JConstructor, JConstructor, Type)]

findConstructor' :: String -> ModelMap -> Maybe JConstructor
findConstructor' k ((JConstructor label rhs superType, JConstructor label' rhs' lhs', t):rest)
  | k == label' = Just $ JConstructor label rhs superType
  | otherwise = findConstructor' k rest
findConstructor' k [] = Nothing -- error $ "missing constructor for " ++ k

synthFromModel :: Exp -> JType -> ModelMap -> Maybe String
synthFromModel Unit (TCon "void" []) m = return ""
synthFromModel (Var x) t m = return x
synthFromModel (K k) t m = synthApp t (K k) [] m
synthFromModel (Op "Nothing") (TCon "Array" _) m = return $ "null"
synthFromModel (Op "Nothing") (TCon "List" _) m = return $ "null"
synthFromModel (Op "Nothing") (TCon "Maybe" _) m = return $ "Option.empty"
synthFromModel (Op "Nothing") (TCon k _) m = return $ "null"
synthFromModel (Op "Nil") (TCon "List" [t]) m = return $ "Collections.emptyList<" ++ (show t) ++ ">()"
synthFromModel (Op "Nil") (TCon "Array" [t]) m = return $ "new " ++ (show t) ++ "[0]"
synthFromModel (Op "Zero") (TCon "int" []) m = return $ "0"
synthFromModel (Op "Zero") (TCon "long" []) m = return $ "0L"
synthFromModel (Op "True") (TCon "boolean" []) m = return $ "true"
synthFromModel (Op "False") (TCon "boolean" []) m = return $ "false"
synthFromModel (App e1 e2) t m = synthApp t e1 [e2] m
synthFromModel e t m = error $ "missing synth " ++ show e ++ " :: " ++ show t

synthApp :: JType -> Exp -> [Exp] -> ModelMap -> Maybe String
synthApp t (App e1 e2) args m = synthApp t e1 (e2:args) m

synthApp (TCon "int" []) (Op "Succ") [e] m = do
  s <- synthFromModel e (TCon "int" []) m
  return $ "(" ++ s ++ " + 1)"
synthApp (TCon "long" []) (Op "Succ") [e] m = do
  s <- synthFromModel e (TCon "long" []) m
  return $ "(" ++ s ++ " + 1L)"

synthApp (TCon "Maybe" [t]) (Op "Just") [e] m = do
  s <- synthFromModel e t m
  return $ "new Option(" ++ s ++ ")"
synthApp (TCon k ts) (Op "Just") [e] m = do
  s <- synthFromModel e (TCon k ts) m
  return s
synthApp (TCon "List" [t]) (Op "++") [e1, e2] m = do
  s1 <- synthFromModel e1 (TCon "List" [t]) m
  s2 <- synthFromModel e2 (TCon "List" [t]) m
  return $ "ListUtil.append(" ++ s1 ++ ", " ++ s2 ++ ")"
synthApp (TCon "List" [t]) (Op ":") [e1, e2] m = do
  s1 <- synthFromModel e1 t m
  s2 <- synthFromModel e2(TCon "List" [t]) m
  return $ "ListUtil.cons(" ++ s1 ++ ", " ++ s2 ++ ")"

synthApp (TCon "Array" [t]) (Op "++") [e1, e2] m = do
  s1 <- synthFromModel e1 (TCon "Array" [t]) m
  s2 <- synthFromModel e2 (TCon "Array" [t]) m
  return $ "ArrayUtil.append(" ++ s1 ++ ", " ++ s2 ++ ")"
synthApp (TCon "Array" [t]) (Op ":") [e1, e2] m = do
  s1 <- synthFromModel e1 t m
  s2 <- synthFromModel e2 (TCon "Array" [t]) m
  return $ "ArrayUtil.cons(" ++ s1 ++ ", " ++ s2 ++ ")"
synthApp t (K k) args m = do
  (JConstructor lhs fields superType) <- findConstructor' k m
  args' <- zipWithM (\arg (x,t) -> synthFromModel arg t m) args fields
  -- assert label <: t || lhs == t
  case args' of
    (a:as) -> do
      let argsString = foldl (\x y -> x ++ ", " ++ y) a as
      return $ "new " ++ lhs ++ "(" ++ argsString ++ ")"
    [] ->
      Nothing
