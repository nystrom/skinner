-- Parse a skin file
module JASTParse (javaAST) where

import Data.Monoid
import Text.Parsec
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

data Decl = Decl1 JConstructor | Decl2 JInterface | Decl3 JEnum

-- parser
-- For now: factories == data types
javaAST :: Parser JAST
javaAST = do
  ws
  rs <- concat <$> many1 (return <$> (Decl1 <$> klass) <|> return <$> (Decl2 <$> abstractKlass) <|> (map Decl3) <$> enum)
  eof
  return $ JAST { jconstructors = decl1 rs,
                  jinterfaces = decl2 rs,
                  jenums = decl3 rs }
  where
    decl1 (Decl1 k:rs) = [k] ++ decl1 rs
    decl1 (_:rs) = decl1 rs
    decl1 [] = []
    decl2 (Decl2 k:rs) = [k] ++ decl2 rs
    decl2 (_:rs) = decl2 rs
    decl2 [] = []
    decl3 (Decl3 k:rs) = [k] ++ decl3 rs
    decl3 (_:rs) = decl3 rs
    decl3 [] = []

enum :: Parser [JEnum]
enum = try $ do
  reserved "enum"
  lhs <- name
  punct "="
  names <- name `sepBy` (punct "|")
  return $ map (\label -> JEnum label (TCon lhs [])) names

abstractKlass :: Parser JInterface
abstractKlass = do
  reserved "abstract"
  reserved "class"
  k <- name
  reserved "extends"
  super <- name
  return $ JInterface k (TCon super [])

klass :: Parser JConstructor
klass = do
  reserved "class"
  k <- name
  punct "("
  fields <- formal `sepBy` (punct ",")
  punct ")"
  reserved "extends"
  super <- name
  return $ JConstructor k fields (TCon super [])

formal :: Parser (String, Type)
formal = do
  typ <- jtype
  x <- name
  return (x, typ)

jtype :: Parser Type
jtype = do
  n <- name
  if n == "List" then do
    punct "<"
    t <- jtype
    punct ">"
    return $ TCon "List" [t]
  else if n == "Option" then do
    punct "<"
    t <- jtype
    punct ">"
    return $ TCon "Option" [t]
  else do
    let t = TCon n []
    option t (do { punct "["; punct "]"; return $ TCon "Array" [t] })

lexer = P.makeTokenParser
  (haskellDef
  { P.reservedNames = ["abstract", "class", "extends", "enum"],
    P.reservedOpNames = ["[", "]", ";", "{", "}", "(", ")", "<", ">"] })

name = P.identifier lexer
reserved = P.reserved lexer
punct = P.reservedOp lexer
stringLiteral = P.stringLiteral lexer
ws = P.whiteSpace lexer