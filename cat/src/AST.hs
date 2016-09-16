module AST where

import Data.Monoid
import Data.List (intercalate)

data Skin = Skin {
  langname :: String,
  interfaces :: [JInterface],
  factories :: [JConstructor],
  tokens :: [(String, Type)],
  aliases :: [[String]],
  templates :: [Template],
  rules :: [Rule],
  jrules :: [JRule]
} deriving Show

data JAST = JAST {
  jconstructors :: [JConstructor],
  jenums :: [JEnum],
  jinterfaces :: [JInterface]
} deriving Show

data JInterface = JInterface String Type
  deriving (Show, Eq, Ord)

data JEnum = JEnum String Type
  deriving (Show, Eq, Ord)

data JConstructor = JConstructor String [JField] Type
  deriving (Show, Eq, Ord)

type JField = (String, Type)

-- Type check the grammar actions.
data Type =
    -- alpha
    TVar Tyvar
    -- TCon tau1 tau2
  | TCon String [Type]
  deriving (Eq, Ord)

funType :: Type -> Type -> Type
funType s t = TCon "->" [s, t]

funType' :: [Type] -> Type -> Type
funType' ss t = foldr funType t ss

instance Show Type where
  show (TVar (Tyvar v)) = v
  show (TCon "->" [s, t]) = (show s) ++ " -> " ++ (show t)
  show (TCon "[]" [t]) = "[" ++ (show t) ++ "]"
  show (TCon "(,)" [s,t]) = "(" ++ (show s) ++ ", " ++ (show t) ++ ")"
  show (TCon "(,,)" [s,t,u]) = "(" ++ (show s) ++ ", " ++ (show t) ++ ", " ++ (show u) ++ ")"
  show (TCon k []) = k
  show (TCon k ts) = k ++ " " ++ (tail $ foldl (\s t -> s ++ " " ++ show t) "" ts)

-- alpha
data Tyvar = Tyvar String
  deriving (Show, Eq, Ord)

data Rule = Rule Type String [(Sym, String)] Exp
  deriving (Show, Eq)

data JRule = JRule Type String [(Sym, String)] JExp
  deriving (Show, Eq)

data Template = Template Type Type [(Sym, String)]
  deriving (Show, Eq)

data Exp = Var String
         | Op String [Exp]
         | K String [Exp]
  deriving (Eq, Ord)

instance Show Exp where
  show (Op ":" [e1, e2]) = show e1 ++ ":" ++ show e2
  show (Op "++" [e1, e2]) = show e1 ++ " ++ " ++ show e2
  show (Op x es) = x ++ " (" ++ intercalate ", " (map show es) ++ ")"
  show (Var x) = x
  show (K k es) = k ++ " (" ++ intercalate ", " (map show es) ++ ")"

data JExp = JNew [JExp] Type
          | JOp String [JExp] Type
          | JK String Type
          | JVar String Type
  deriving (Eq)

instance Show JExp where
  show (JNew es t) = "new " ++ show t ++ "(" ++ intercalate ", " (map show es) ++ ")"
  show (JOp op es t) = op ++ "(" ++ intercalate ", " (map show es) ++ ")" ++ " :: " ++ show t
  show (JK k t) = k ++ " :: " ++ show t
  show (JVar x t) = x ++ " :: " ++ show t

typeof :: JExp -> Type
typeof (JNew es t) = t
typeof (JOp op es t) = t
typeof (JK k t) = t
typeof (JVar x t) = t

data Sym = Nonterminal String | Terminal String
  deriving (Show, Eq, Ord)

symname :: Sym -> String
symname (Nonterminal x) = x
symname (Terminal x) = x

instance Ord Rule where
  compare (Rule t1 lhs1 rhs1 _) (Rule t2 lhs2 rhs2 _) =
    (lhs1 `compare` lhs2) `mappend` (rhs1 `compare` rhs2)
