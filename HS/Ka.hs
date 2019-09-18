module Ka where

x, y, z :: Int
(x, y, z) = (11, 45, 14)

s1, s2 :: [Int]
s1 = [1..10]
s2 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

f :: [Int] -> [Int]
f [ ] = [ ]
f [e] = [e]
f (e : _ : s) = e : f s

-- (>*<)
-- ,[.>,]

g :: [Int] -> [Int]
g = map fst . filter ((0 ==) . flip mod 2 . snd) . zip [1..]

-- (define (f l)
--     (if (null? (cdr l))
--         l
--         (cons (car l) (f (caddr l)))))

h :: Maybe Int -> Maybe Int -> Maybe Int
h mx my = do
    x <- mx
    y <- my
    pure $ x + y


-- h = !mx + !my
