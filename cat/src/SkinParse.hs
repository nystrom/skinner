-- Parse a skin file
module SkinParse (skin) where

import Data.Monoid
import Text.Parsec hiding (token, label, tokens)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.String
import Control.Applicative((<$>), (<*>), (<*), (*>), (<$))
import Control.Monad.State
import Data.List ((\\), find, sortBy, minimum, minimumBy)
import Data.Char (toLower, toUpper, isLower, isUpper)
import Data.Maybe (catMaybes, listToMaybe)
import Debug.Trace (trace)

import Aliases
import AST

-- printf debugging
debug :: (Monad m) => String -> m ()
debug s = trace s (return ())

-- skin parser
skin :: Parser Skin
skin = do
  ws
  reserved "language"
  langname <- name
  aliases <- many alias
  reserved "ast"
  datatypes <- many datatype
  reserved "lexer"
  tokens <- many token
  reserved "template"
  templates <- many template
  reserved "grammar"
  rules <- many rule
  eof
  return $ Skin { langname = langname,
                  interfaces = map fst datatypes,
                  factories = concatMap snd datatypes,
                  tokens = tokens,
                  aliases = aliases,
                  templates = templates,
                  rules = concat rules }

token :: Parser (String, Type)
token = reserved "token" *> do { t <- name; n <- name; return (n, TCon t []) }

alias :: Parser [String]
alias = do
    reserved "alias"
    words <- split <$> manyTill anyChar (try newline)
    ws
    -- words <- many name
    return $ filter (/= "") (map (map toLower) words)
  where
    split :: String -> [String]
    split "" = []
    split (' ':xs) = "" : split (dropWhile (==' ') xs)
    split (x:xs) = case words of
        [] -> [x:""]
        (w:ws) -> (x:w):ws
      where
        words = split xs

template :: Parser Template
template = do
  t <- typ []
  punct "->"
  t' <- typ []
  punct "::="
  rhs <- rhsWithoutAction
  punct ";"
  return $ Template t t' rhs

rule :: Parser [Rule]
rule = do
  t <- typ []
  lhs <- name
  punct "::="
  rhss <- rhs `sepBy` (punct "|")
  punct ";"
  return $ map (\(rhs, action) -> Rule t lhs rhs action) rhss

rhs :: Parser ([(Sym, String)], Exp)
rhs = do
  syms <- many (try $ nonterm <|> term)
  a <- action
  return $ (syms, a)

rhsWithoutAction :: Parser [(Sym, String)]
rhsWithoutAction = do
  syms <- many (try $ nonterm <|> term)
  return $ syms

action :: Parser Exp
action = do
  punct "{"
  e <- expression
  punct "}"
  ws
  return e

expression :: Parser Exp
expression = try $ cons `chainr1`
  (do { punct "++"; return (\x y -> App (App (Op "++") x) y) })

cons :: Parser Exp
cons = try $ application `chainr1`
  (do { punct ":"; return (\x y -> App (App (Op ":") x) y) })

application :: Parser Exp
application = try $ do
  e <- primary
  es <- many primary
  return $ foldl App e es

primary :: Parser Exp
primary = try (nameExp <|> list expressions <|> tuple expressions)

nameExp :: Parser Exp
nameExp = try $ do
  x <- name
  return $ case x of
    "Nil" -> Op "Nil"
    "Nothing" -> Op "Nothing"
    "Just" -> Op "Just"
    "True" -> Op "True"
    "False" -> Op "False"
    x | isUpper $ head x -> K x
    x -> Var x

number :: Parser Int
number = read <$> many1 digit <* ws

expressions :: Parser [Exp]
expressions = try $ expression `sepBy` (punct ",")

list :: Parser [Exp] -> Parser Exp
list p = do
  punct "["
  r <- p
  punct "]"
  return $ foldr (\x y -> App (App (Op ":") x) y) (Op "Nil") r

tuple :: Parser [Exp] -> Parser Exp
tuple p = do
  punct "("
  r <- p
  punct ")"
  case r of
    [] -> return Unit
    (x:[]) -> return x
    (x:y:[]) -> return $ App (App (Op "(,)") x) y
    (x:y:z:[]) -> return $ App (App (App (Op "(,,)") x) y) z
    _ -> error "tuples larger than 3 not supported"

term :: Parser (Sym, String)
term = do
  x <- stringLiteral
  option (Terminal x, "_")
    (punct ":" *> do { k <- name; return (Terminal x, k)})

nonterm :: Parser (Sym, String)
nonterm = do
  x <- name
  if x == map toUpper x then
    option (Terminal x, "_")
      (punct ":" *> do { k <- name; return (Terminal x, k)})
  else do
    option (Nonterminal x, "_")
      (punct ":" *> do { k <- name; return (Nonterminal x, k)})

datatype :: Parser (JInterface, [JConstructor])
datatype = try $ do
  reserved "data"
  lhs <- name
  params <- many name
  punct "="
  cases <- (kase params) `sepBy` (punct "|")
  return $ (JInterface lhs (TCon "Object" []), map (\(label, children) -> JConstructor label (toFields children) (TCon lhs [])) cases)

-- fixme: use actual field names for records
-- for Java code Add(Exp, Exp) { left = a1, right = a2 }
--           --> Add { left :: Exp, right :: Exp }
toFields :: [Type] -> [JField]
toFields children = [("_" ++ show x, t) | (x, t) <- [1..] `zip` children]

kase :: [String] -> Parser (String, [Type])
kase params = do
  label <- name
  rhs <- many (typ params)
  return (label, rhs)

typ :: [String] -> Parser Type
typ params = try $
  (do
    x <- name
    if x `elem` params then
      return $ TVar (Tyvar x)
    else
      return $ TCon x []) <|>
  (do
    punct "["
    t <- typ params
    punct "]"
    return $ TCon "List" [t]) <|>
  (do
    punct "("
    x <- name
    ts <- many (typ params)
    punct ")"
    return $ TCon x ts)

lexer = P.makeTokenParser
  (haskellDef
  { P.reservedNames = ["data", "alias", "language", "grammar", "token", "lexer", "template"],
    P.reservedOpNames = ["=", "|", "[", "]", "::=", ";", "?", "*", "+", "{", "}", "(", ")", ":"] })

name = P.identifier lexer
reserved = P.reserved lexer
punct = P.reservedOp lexer
stringLiteral = P.stringLiteral lexer
ws = P.whiteSpace lexer
