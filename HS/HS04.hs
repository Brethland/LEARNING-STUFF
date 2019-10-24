module HS04 where

qsort :: [Integer] -> [Integer]
qsort [] = []
qsort (x : xs) = (filter (< x) xs) ++ (x : (filter (>= x) xs))

