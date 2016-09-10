-- This module handles matching names with aliases.
-- For instance Plus and Add are aliases and so matching PlusExp with AddExp
-- should cost nothing.
module Aliases (Word, Aliases, matchNameWithAliases) where

import Prelude hiding (Word)
import Data.List ((\\), find, sortBy, minimum, minimumBy, nub)
import Data.Char (toLower, toUpper, isLower, isUpper, isSpace)
import Data.Maybe (catMaybes, listToMaybe)
import Debug.Trace (trace)
import Data.Set (Set)
import qualified Data.Set as Set

type Word = String
type Aliases = [Word]

expandAliases :: [Aliases] -> Word -> [Word]
expandAliases [] word = [word]
expandAliases (aliases:aliasess) word = aliasesOf aliases word ++ expandAliases aliasess word
  where
    aliasesOf :: Aliases -> Word -> [Word]
    aliasesOf aliases word = if word `elem` aliases then aliases else []

-- Break a name like PlusExp or Plus_Exp into words: [Plus, Exp]
breakNameIntoWords "" = []
-- under_score
breakNameIntoWords ('_':xs) = "" : breakNameIntoWords (dropWhile (=='_') xs)
-- two words
breakNameIntoWords (x:xs) | isSpace x = "" : breakNameIntoWords (dropWhile isSpace xs)
-- CamelCase
breakNameIntoWords (x:y:ys)
  | isLower x && isUpper y = (x:"") : breakNameIntoWords (y:ys)
--
breakNameIntoWords (x:xs) = case words of
    [] -> [x:""]
    (w:ws) -> (x:w):ws
  where
    words = breakNameIntoWords xs

matchNameWithAliases :: [[String]] -> String -> String -> Int
matchNameWithAliases aliases x y =
    {-
    trace ("matchNameWithAliases " ++ x ++ " ~~ " ++ y ++ ": " ++ show r) $
      trace ("  aliases for " ++ (show ys) ++ " ===> " ++ (show as)) r
      -}
    r
  where
    r = Set.size $ Set.fromList xs `Set.difference` Set.fromList as
    xs = breakNameIntoWords (map toLower x)
    ys = breakNameIntoWords (map toLower y)
    as = nub $ concatMap (expandAliases aliases) ys
    bs = nub $ concatMap (expandAliases aliases) xs

-- editDistanceString :: String -> String -> Int
-- editDistanceString = editDistance (const 1) (const (const 10))
--
-- editDistanceStrings = editDistance length editDistanceString
--
-- editDistance :: Eq a => (a -> Int) -> (a -> a -> Int) -> [a] -> [a] -> Int
-- editDistance cost cost2 [] [] = 0
-- editDistance cost cost2 (x:xs) [] = sum (map cost (x:xs))
-- editDistance cost cost2 [] (x:xs) = sum (map cost (x:xs))
-- editDistance cost cost2 (x:xs) (y:ys)
--   | x == y    = editDistance cost cost2 xs ys
--   | otherwise = minimum [
--       (cost x) + (editDistance cost cost2 xs (y:ys)),
--       (cost y) + (editDistance cost cost2 (x:xs) ys),
--       (cost2 x y) + (editDistance cost cost2 xs ys)
--     ]
