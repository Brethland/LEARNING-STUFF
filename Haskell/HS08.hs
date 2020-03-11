module HS08 where

import Prelude

fix :: (a -> a) -> a
fix f = let x = f x in x

reverse' :: ([a] -> [a]) -> [a] -> [a]
reverse' _ []       = []
reverse' f (a : as) = f as ++ [a]

foldr' :: ((a -> b -> b) -> b -> [a] -> b) -> (a -> b -> b) -> b -> [a] -> b
foldr' _ _ d []       = d
foldr' f o d (a : as) = o a (f o d as)

fixFoldr :: (a -> b -> b) -> b -> [a] -> b
fixFoldr = fix foldr'
fixReverse :: [a] -> [a]
fixReverse = fix reverse'

