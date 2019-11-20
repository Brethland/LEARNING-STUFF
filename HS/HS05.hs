module Ha where

import Control.Monad

-- class Show a where
--     show :: a -> String

data Color = R | G | B -- deriving Show

instance Show Color where
    show R = "Red"
    show G = "Green"
    show B = "Blue"

-- instance Read Color where
--     reads "Red"   = R
--     reads "Green" = G
--     reads "Blue"  = B

-- data Either a b = Left a | Right b

-- 1. fmap id = id
-- 2. fmap (f . g) = fmap f . fmap g

-- Functor
-- Applicative

-- 2. pure (.) <*> u <*> v
-- f ((b -> c) -> ( (a -> b) -> (a -> c) ) )
-- f (b -> c) -> f ((a -> b) -> (a -> c))

-- (->) r impla
-- K x y = x
-- S x y z = x z (y z)

safeAdd :: Maybe Int -> Maybe Int -> Maybe Int
-- safeAdd mx my = case mx of
--     Nothing -> Nothing
--     Just x  -> case my of
--         Nothing -> Nothing
--         Just y  -> Just $ x + y
-- safeAdd mx my = 
--     mx `evalSeq` \x -> 
--     my `evalSeq` \y -> 
--     Just (x + y)
-- safeAdd mx my =
--     mx >>= \x ->
--     my >>= \y ->
--     return $ x + y
safeAdd mx my = do {
    x <- mx; -- mx >>= \x ->
    y <- my;
    -- m :: Monad m => m ()
    return $ x + y; }


evalSeq :: Maybe Int -> (Int -> Maybe Int) -> Maybe Int
evalSeq m f = case m of
    Nothing -> Nothing
    Just a  -> f a

main :: IO ()
main = do
    putStrLn "Hello, do!"
    line <- getLine
    putStrLn line
    return ()

myJoin :: Monad m => m (m a) -> m a
myJoin mmx = do
    mx <- mmx
    x <- mx
    pure x
-- myJoin mmx = pure !(!mmx) -- Idris

myWTF :: Monad m => m (a -> b) -> m a -> m b
myWTF mf ma = do
    f <- mf
    a <- ma
    pure $ f a
-- myWTF mf ma = pure (!mf !ma)

testArr :: [Int]
-- testArr = [ 10 * x + y | x <- [1..3], y <- [4..6], odd (x + y) ]
testArr = do
    x <- [1, 2, 3]
    y <- [4, 5, 6]
    guard $ odd $ x + y
    return $ 10 * x + y


-- a0 -> a1 -> a2
myLiftA1 :: (Applicative f) => (a -> b) -> f a -> f b
myLiftA1 op fa = op <$> fa

myLiftA2 :: (Applicative f) => (a -> b -> c) -> f a -> f b -> f c
myLiftA2 op fa fb = op <$> fa <*> fb

myLiftA3 :: (Applicative f) => (a -> (b -> (c -> d))) -> f a -> f b -> f c -> f d
myLiftA3 op fa fb fc = op <$> fa <*> fb <*> fc

-- Writer Monad
-- Reader Monad
-- State  Monad