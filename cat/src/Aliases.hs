-- This module handles matching names with aliases.
-- For instance Plus and Add are aliases and so matching PlusExp with AddExp
-- should cost nothing.
module Aliases (Word, Aliases, matchNameWithAliases, Wordy(..), breakNameIntoWords, expandAliases) where

import Prelude hiding (Word)
import Data.List (nub, inits)
import Data.Char (toLower, isLower, isUpper, isSpace, isDigit)
import Debug.Trace (trace)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (liftM2)

class Wordy a where
  toBagOfWords :: a -> [Word]

type Word = String
type Aliases = [Word]

prefixes word = filter (\w -> 3 <= length w && length w <= 6) (inits word)
contraction (x:xs) = x:filter (not . (`elem` "aeiou")) xs
contraction' word = removeRepeats $ contraction word

removeRepeats [] = []
removeRepeats [x] = [x]
removeRepeats (x:y:ys) | x == y = removeRepeats (y:ys)
                       | otherwise = x : removeRepeats (y:ys)

aliasesOf :: Aliases -> Word -> [Word]
aliasesOf aliases word = if word `elem` aliases then concatMap variants aliases else []

variants word = nub $ word : prefixes word ++ prefixes (contraction word) ++ prefixes (contraction' word)

expandAliases :: [Aliases] -> Word -> [Word]
expandAliases [] word = [word]
expandAliases (aliases:aliasess) word = nub $ aliasesOf aliases word ++ expandAliases aliasess word


chooseAlias :: [[String]] -> String -> String
chooseAlias aliases word = maximum $ expandAliases aliases word



-- Break a name like PlusExp or Plus_Exp into words: [Plus, Exp]
breakNameIntoWords :: String -> [String]
breakNameIntoWords w = filter (not . null) (go w)
  where
    go "" = []
    -- prime
    go ('\'':xs) = "" : breakNameIntoWords (dropWhile (== '\'') xs)
    -- under_score
    go ('_':xs) = "" : breakNameIntoWords (dropWhile (== '_') xs)
    -- two words
    go (x:xs) | isSpace x = "" : breakNameIntoWords (dropWhile isSpace xs)
    -- digits
    go (x:xs) | isDigit x = "" : breakNameIntoWords (dropWhile isDigit xs)
    -- CamelCase
    go (x:y:ys) | isLower x && isUpper y = (x:"") : breakNameIntoWords (y:ys)
    -- otherwise
    go (x:xs) = case go xs of
                  [] -> [x:""]
                  (w:ws) -> (x:w):ws

matchWordies :: Wordy a => [[String]] -> a -> a -> Double
matchWordies aliases x y = do
  let xs = toBagOfWords x
  let ys = toBagOfWords y
  let xys = liftM2 (,) xs ys
  product $ map (uncurry (matchNameWithAliases aliases)) xys

-- TODO: a single word might expand to multiple words
matchNameWithAliases :: [[String]] -> String -> String -> Double
matchNameWithAliases aliases x y =
    1 - index
  where
    xs = map (map toLower) $ breakNameIntoWords x
    ys = map (map toLower) $ breakNameIntoWords y

    -- replace each word with a representative alias
    repXs = map (chooseAlias aliases) xs
    repYs = map (chooseAlias aliases) ys

    -- return the Jaccard index (size of the intersection / size of the union)
    xset = Set.fromList repXs
    yset = Set.fromList repYs

    -- Jaccard index
    index = fromIntegral (Set.size (xset `Set.intersection` yset)) / fromIntegral (Set.size (xset `Set.union` yset))
