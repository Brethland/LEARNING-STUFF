module MyParsec where

-- Parser Combinator

newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

-- data Point = Point {
--     x :: Double,
--     y :: Double
-- }

instance Functor Parser where
    fmap f p = Parser $ \str ->
        case runParser p str of
            Just (a, s) -> Just (f a, s)
            Nothing     -> Nothing
-- instance Applicative Parser where
--     <*> f p = Parser $ \str ->
--         case runParser p str of
--             Just(a, s) -> Just(pure a, s)
--             Nothing    -> Nothing 

-- Functor => Applicative => Monad

-- >>=

p :: Monad m => m (a -> b) -> m a -> m b
p mf ma = do
    f <- mf
    a <- ma
    return $ f a


-- Before 2014

-- Functor => Applicative
-- Functor => Monad