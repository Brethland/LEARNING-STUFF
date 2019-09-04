{-# LANGUAGE BangPatterns #-}

module Ja where

c :: Maybe Int -> Maybe Int -> Maybe Int
c mx my = do
    x <- mx
    y <- my
    pure $ x + y
-- c mx my = case (mx, my) of
--     (Just x, Just y) -> Just (x + y)
--     _                -> Nothing
-- c = liftA2 (+)

fact :: Integer -> Integer
fact n | n <= 0 = 1
       | True   = undefined `seq` (n * (fact $ n - 1))

cond :: Bool -> a -> a -> a
cond True  !a !_ = a
cond False !_ !a = a

-- c _ _                                 = Nothing
-- main :: IO()
-- main = do
--     c ma mb
--     where ma <- IO mb <- IO

-- (cond #f undefined 1)

-- add(1)

id :: a -> a
id a = a
union :: f -> g -> x -> y
union a b x = a (b x)
