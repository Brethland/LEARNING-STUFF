module ParserTest where

import Text.ParserCombinators.Parsec

myOneOf :: String -> Parser Char
myOneOf  []      = error ""
myOneOf (x : xs) = char x <|> myOneOf xs

p1 :: Parser String
p1 = do
    x <- oneOf $ ['a'..'z'] ++ ['A'..'Z']
    s <- many alphaNum
    return (x : s)