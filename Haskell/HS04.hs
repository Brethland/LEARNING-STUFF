module Syntactic where

data Stack = E | E' | T | T' | F | I | PLUS | MULT | LB | RB | END deriving (Show, Eq)

type ParseState = ([Stack], String)

llMatchingStep :: ParseState -> ParseState
llMatchingStep (xs, [])   = (xs, "#")
llMatchingStep ([], syms) = ([END], syms)
llMatchingStep ([END], "#") = ([END], "#")
llMatchingStep ((x : xs), (sym : syms)) = case (x , sym) of
    (E    , 'i')   -> ((T : (E' : xs)), (sym : syms))
    (E    , '(')   -> ((T : (E' : xs)), (sym : syms))
    (E'   , '+')   -> ((PLUS : (T : (E' : xs))), (sym : syms))
    (E'   , ')')   -> (xs, (sym : syms))
    (E'   , '#')   -> (xs, (sym : syms))
    (T    , 'i')   -> ((F : (T' : xs)), (sym : syms))
    (T    , '(')   -> ((F : (T' : xs)), (sym : syms))
    (T'   , '+')   -> (xs, (sym : syms))
    (T'   , '*')   -> ((MULT : (F : (T' : xs))), (sym : syms))
    (T'   , ')')   -> (xs, (sym : syms))
    (T'   , '#')   -> (xs, (sym : syms))
    (F    , 'i')   -> ((I : xs), (sym : syms))
    (F    , '(')   -> ((LB : (E : (RB : xs))), (sym : syms))
    (I    , 'i')   -> (xs, syms)
    (PLUS , '+')   -> (xs, syms)
    (MULT , '*')   -> (xs, syms)
    (RB   , ')')   -> (xs, syms)
    (LB   , '(')   -> (xs, syms)
    (END  , _  )   -> ((E : (END : xs)), (sym : syms))
    (_    , _  )   -> ((x : xs), (sym : syms))

llIdentify :: ParseState -> Bool
llIdentify ([END], "#") = True
llIdentify _            = False

-- llMatchingHelper :: (ParseState, ParseState) -> Bool
-- llMatchingHelper (old, new) = if old == new 
--     then llIdentify new
--     else llMatchingHelper (new, llMatchingStep new)

-- llMatching :: String -> Bool
-- llMatching str = llMatchingHelper (p, llMatchingStep p)
--     where p = ([], str)

llMatchingStepImpure :: ParseState -> IO ParseState
llMatchingStepImpure p = do
    print p
    return $ llMatchingStep p

llMatchingHelperImpure :: (IO ParseState, IO ParseState) -> IO Bool
llMatchingHelperImpure (mOld, mNew) = do
    old <- mOld
    new <- mNew
    if (old == new)
        then return $ llIdentify new
        else llMatchingHelperImpure (return new, llMatchingStepImpure new)

llMatchingImpure :: String -> IO Bool
llMatchingImpure str = llMatchingHelperImpure (return p, llMatchingStepImpure p)
    where p = ([], str)

main :: IO Bool
main = llMatchingImpure "(i)*i*((i+i))"