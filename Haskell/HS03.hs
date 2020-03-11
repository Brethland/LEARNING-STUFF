module HS03 where

import Prelude hiding((++),filter,Eq,(==),(/=))

last' :: [a] -> Maybe a
last' [] = Nothing
last' [a] = Just a
last' (_ : xs) = last' xs

(++) :: [a] -> [a] -> [a] 
[] ++ a = a
(x : xs) ++ a = x : (xs ++ a) 

find :: (a -> Bool) -> [a] -> Maybe a
find _ [] = Nothing
find p (x : xs) = case (p x) of
    True ->    Just x
    _    -> find p xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x : xs) = case (p x) of
    True -> x : filter p xs
    _    ->     filter p xs

length :: [a] -> Integer
length = go 0
    where
        go n []       = n
        go n (_ : xs) = go (n + 1) xs

sum :: [Integer] -> Integer
sum = go 0
    where 
        go n []       = n
        go n (x : xs) = go (n + x) xs

data Tree a 
    = Empty 
    | Node a
    | Branch (Tree a) (Tree a)

newtype ReaderT a b c = ReaderT (a -> b c)

newtype Fix a = Fix (a (Fix a))

class Eq a where
    (==), (/=) :: a -> a -> Bool
    x /= y      = not (x == y)
    x == y      = not (x /= y)
    {-# MINIMAL (==) | (/=) #-}

data Height = Height Double

instance Eq a => Eq [a] where
    []             == [] = True
    (x : xs) == (y : ys) = x == y && xs == ys
    _              == _ = False


