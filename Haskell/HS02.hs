module HS02 where

data Point = Point Double Double deriving Show

data RGB = 
    Red |
    Green |
    Blue deriving Show

data PointRecord = PointRecord {
    getX :: Double,
    getY :: Double
} deriving Show

data Point' a = Point' a a

inflist :: Num a => [a]
inflist = 1 : inflist

newtype StateT s m a = StateT (s -> m (s , a))