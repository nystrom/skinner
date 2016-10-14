-- Parse a skin file
module SkinParse (skin) where

import Data.Monoid
import Text.Parsec hiding (token, label, tokens)
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.String
import Control.Applicative((<$>), (<*>), (<*), (*>), (<$))
import Control.Monad.State
import Data.List (nub)
import Data.Char (toLower, toUpper, isLower, isUpper)
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
  tokens <- many token
  templates <- many template
  reserved "grammar"
  rules <- many rule
  eof
  return Skin { langname = langname,
                  interfaces = nub $ concatMap fst datatypes,
                  factories = nub $ concatMap snd datatypes,
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
  reserved "template"
  t <- typ []
  punct "->"
  t' <- typ []
  punct "::="
  (rhs, action) <- rhs
  punct ";"
  return $ Template t t' rhs action

rule :: Parser [Rule]
rule = do
  t <- typ []
  lhs <- name
  punct "::="
  rhss <- rhs `sepBy` punct "|"
  punct ";"
  return $ map (uncurry (Rule t lhs)) rhss

rhs :: Parser ([(Sym, String)], JExp)
rhs = do
  syms <- many (try $ nonterm <|> term)
  a <- action
  return (syms, a)

rhsWithoutAction :: Parser [(Sym, String)]
rhsWithoutAction = do
  syms <- many (try $ nonterm <|> term)
  return syms

action :: Parser JExp
action = do
  punct "{"
  e <- expression
  punct "}"
  ws
  return e

expression :: Parser JExp
expression = try $ cons `chainr1`
  (do { punct "++"; return (\x y -> JOp "++" [x, y] TBoh) })

cons :: Parser JExp
cons = try $ try (application <|> primary) `chainr1`
  (do { punct ":"; return (\x y -> JOp ":" [x, y] TBoh) })

variable :: Parser JExp
variable = try $ do
  x <- name
  case x of
    "Nil" -> return $ JK "Nil" TBoh
    "Nothing" -> return $ JK "Nothing" TBoh
    "True" -> return $ JK "true" (TCon "boolean" [])
    "False" -> return $ JK "false" (TCon "boolean" [])
    x @ (y:_) | isUpper y -> do
      return $ JOp x [] TBoh
    x -> return $ JVar x TBoh

application :: Parser JExp
application = try $ do
  x <- name
  case x of
    "Nil" -> return $ JK "Nil" TBoh
    "Nothing" -> return $ JK "Nothing" TBoh
    "True" -> return $ JK "true" (TCon "boolean" [])
    "False" -> return $ JK "false" (TCon "boolean" [])
    "Just" -> do
      e <- primary
      return $ JOp "Just" [e] TBoh
    x @ (y:_) | isUpper y -> do
      es <- many primary
      return $ JOp x es TBoh
    x -> return $ JVar x TBoh

primary :: Parser JExp
primary = try (variable <|> list expressions <|> tuple expressions)

number :: Parser Int
number = read <$> many1 digit <* ws

expressions :: Parser [JExp]
expressions = try $ expression `sepBy` punct ","

list :: Parser [JExp] -> Parser JExp
list p = do
  punct "["
  r <- p
  punct "]"
  return $ foldr (\x y -> JOp ":" [x, y] TBoh) (JK "Nil" TBoh) r

tuple :: Parser [JExp] -> Parser JExp
tuple p = do
  punct "("
  r <- p
  punct ")"
  case r of
    [] -> return $ JK "()" (TCon "void" [])
    [x] -> return x
    [x,y] -> return $ JOp "(,)" [x,y] (TCon "(,)" [typeof x, typeof y])
    [x,y,z] -> return $ JOp "(,,)" [x,y,z] (TCon "(,,)" [typeof x, typeof y, typeof z])
    _ -> error "tuples larger than 3 not supported"

term :: Parser (Sym, String)
term = do
  x <- stringLiteral
  option (Literal x, "_")
    (punct ":" *> do { k <- name; return (Literal x, k)})

nonterm :: Parser (Sym, String)
nonterm = do
  x <- name
  if x == map toUpper x then
    option (Terminal x, "_")
      (punct ":" *> do { k <- name; return (Terminal x, k)})
  else
    option (Nonterminal x, "_")
      (punct ":" *> do { k <- name; return (Nonterminal x, k)})

datatype :: Parser ([JInterface], [JConstructor])
datatype = try $ do
  reserved "data"
  lhs <- name
  params <- many name
  punct "="
  cases <- kase params `sepBy` punct "|"
  -- return $ (JInterface lhs (TCon "Object" []) :
  --    map (\(label, children) -> JInterface label (TCon lhs [])) (filter (\(label, _) -> label /= lhs) cases),
  --    map (\(label, children) -> JConstructor label (toFields children) (TCon label [])) cases)
  return ([JInterface lhs (TCon "Object" [])],
     map (\(label, children) -> JConstructor label (toFields children) (TCon lhs [])) cases)

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
  { P.reservedNames = ["data", "alias", "language", "grammar", "token", "template"],
    P.reservedOpNames = ["=", "|", "[", "]", "::=", ";", "?", "*", "+", "{", "}", "(", ")", ":"] })

name = P.identifier lexer
reserved = P.reserved lexer
punct = P.reservedOp lexer
stringLiteral = P.stringLiteral lexer
ws = P.whiteSpace lexer
