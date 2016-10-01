module AST where

import           Data.List   (intercalate)
import           Data.Monoid

data Skin = Skin {
  langname   :: String,
  interfaces :: [JInterface],
  factories  :: [JConstructor],
  tokens     :: [(String, Type)],
  aliases    :: [[String]],
  templates  :: [Template],
  rules      :: [Rule]
} deriving Show

data JAST = JAST {
  jinterfaces   :: [JInterface],
  jconstructors :: [JConstructor],
  jenums        :: [JEnum],
  jexps         :: [JExp],
  jheader       :: String,
  jbody         :: String
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
  | TBoh
  deriving (Eq, Ord)

funType :: Type -> Type -> Type
funType s t = TCon "->" [s, t]

funType' :: [Type] -> Type -> Type
-- funType' ss t = foldr funType t ss
funType' ss t = funType (tupleType ss) t

tupleType :: [Type] -> Type
tupleType [] = TCon "void" []
tupleType [s] = s
tupleType (s:ss) = TCon label ss
  where
    label = "(" ++ map (const ',') ss ++ ")"

instance Show Type where
  show (TVar (Tyvar v)) = v
  show (TCon "->" [s, t]) = show s ++ " -> " ++ show t
  show (TCon "List" [t]) = "[" ++ show t ++ "]"
  show (TCon "(,)" [s,t]) = "(" ++ show s ++ ", " ++ show t ++ ")"
  show (TCon "(,,)" [s,t,u]) = "(" ++ show s ++ ", " ++ show t ++ ", " ++ show u ++ ")"
  show (TCon k []) = k
  show (TCon k ts) = k ++ " " ++ (tail $ foldl (\s t -> s ++ " " ++ show t) "" ts)
  show TBoh = "boh!"

-- alpha
data Tyvar = Tyvar String
  deriving (Show, Eq, Ord)

data Rule = Rule Type String [(Sym, String)] JExp
  deriving (Show, Eq)

ruleIsEssential :: Rule -> Bool
ruleIsEssential (Rule _ _ _ e) = callsFactory e
  where
    callsFactory (JNew _ _) = True
    callsFactory (JOp _ es _) = any callsFactory es
    callsFactory (JK "Nil" _) = False
    callsFactory (JK "Nothing" _) = False
    callsFactory (JK _ _) = True
    callsFactory (JVar _ _) = False

data Template = Template Type Type [(Sym, String)] JExp
  deriving (Show, Eq)

data JExp = JNew [JExp] Type
          | JOp String [JExp] Type
          | JK String Type
          | JVar String Type
  deriving (Eq)

instance Show JExp where
  show (JNew es t) = "new " ++ show t ++ "(" ++ intercalate ", " (map show es) ++ ")"
  show (JOp op es t) = op ++ "(" ++ intercalate ", " (map show es) ++ ")" ++ " :: " ++ show t
  show (JK "()" (TCon "void" [])) = "()"
  show (JK "true" (TCon "boolean" [])) = "true"
  show (JK "false" (TCon "boolean" [])) = "false"
  show (JK k t) = k ++ " :: " ++ show t
  show (JVar x t) = x ++ " :: " ++ show t

typeof :: JExp -> Type
typeof (JNew es t)   = t
typeof (JOp op es t) = t
typeof (JK k t)      = t
typeof (JVar x t)    = t

data Sym = Nonterminal String | Terminal String
  deriving (Show, Eq, Ord)

symname :: Sym -> String
symname (Nonterminal x) = x
symname (Terminal x)    = x

instance Ord Rule where
  compare (Rule t1 lhs1 rhs1 _) (Rule t2 lhs2 rhs2 _) =
    (lhs1 `compare` lhs2) `mappend` (rhs1 `compare` rhs2)
