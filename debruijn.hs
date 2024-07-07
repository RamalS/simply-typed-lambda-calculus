module DeBruijn where

import Data.Char (chr)

findInd :: Char -> Int -> [Char] -> Int
findInd c i [] = i
findInd c i (x:xs)
    | c == x = i
    | otherwise = findInd c (i + 1) xs

intToChar :: Int -> Char
intToChar n
  | n >= 0 && n <= 9 = chr (n + 48)
  | otherwise = error "Input is not a single digit"


dbruj :: [Char] -> [Char] -> [Char] -> [Char]
dbruj new llam [] = new
dbruj new llam [b] = new ++ [b]
dbruj new llam [b, t] = new ++ [b, t]
-- dbruj new llam [b] = llam
-- dbruj new llam [b, t] = llam
dbruj new llam (b:t:a:xs)
    | b == '\\' = dbruj (new ++ [b]) (llam ++ [t]) (t : a : xs)
    | b == ' ' && a `elem` " :)" && t `elem` llam = dbruj (new ++ [b,  intToChar varInd]) llam (a : xs)
    | b == ')' = dbruj (new ++ [b]) (init llam) (t : a : xs)
    | otherwise = dbruj (new ++ [b]) llam (t : a : xs)
    where ind = findInd t 0 llam
          varInd = length llam - ind - 1