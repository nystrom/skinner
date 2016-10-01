-- This module handles matching names with aliases.
-- For instance Plus and Add are aliases and so matching PlusExp with AddExp
-- should cost nothing.
module Aliases (Word, Aliases, matchNameWithAliases, Wordy(..), breakNameIntoWords, expandAliases) where

import Prelude hiding (Word)
import Data.List ((\\), find, sortBy, minimum, minimumBy, nub)
import Data.Char (toLower, toUpper, isLower, isUpper, isSpace)
import Data.Maybe (catMaybes, listToMaybe)
import Debug.Trace (trace)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (liftM2)

class Wordy a where
  toBagOfWords :: a -> [Word]

type Word = String
type Aliases = [Word]

expandAliases :: [Aliases] -> Word -> [Word]
expandAliases [] word = [word]
expandAliases (aliases:aliasess) word = nub $ aliasesOf aliases word ++ expandAliases aliasess word
  where
    aliasesOf :: Aliases -> Word -> [Word]
    aliasesOf aliases word = if word `elem` aliases then aliases else []

breakNameIntoWords :: String -> [String]
-- Break a name like PlusExp or Plus_Exp into words: [Plus, Exp]
breakNameIntoWords "" = []
-- under_score
breakNameIntoWords ('_':xs) = "" : breakNameIntoWords (dropWhile (== '_') xs)
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

matchWordies :: Wordy a => [[String]] -> a -> a -> Double
matchWordies aliases x y = do
  let xs = toBagOfWords x
  let ys = toBagOfWords y
  let xys = liftM2 (,) xs ys
  product $ map (uncurry (matchNameWithAliases aliases)) xys

-- Compute a cost between 0 and 1 for a string match
-- Exp -> Expression should cost 0
-- Statement -> Exp should cost 0.5 (for example)
-- Plus -> Times should cost 1
matchNameWithAliases :: [[String]] -> String -> String -> Double
matchNameWithAliases aliases x y =
    product costs
  where
    xs = map (map toLower) $ breakNameIntoWords x
    ys = map (map toLower) $ breakNameIntoWords y
    xass = map (expandAliases aliases) xs
    yass = map (expandAliases aliases) ys
    xyass = liftM2 (,) xass yass
    sd a b = (a `Set.difference` b) `Set.union` (b `Set.difference` a)
    cost xas yas = size (Set.fromList xas `sd` Set.fromList yas) / size (Set.fromList xas `Set.union` Set.fromList yas)
    size s = fromIntegral (Set.size s)
    costs = map (uncurry cost) xyass
