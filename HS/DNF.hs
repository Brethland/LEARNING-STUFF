module DNF where



data Prop = Prop Char Bool deriving Show

and :: Prop -> Prop -> Bool

Prop _ False `and` _          = False
_ `and` Prop _ False          = False
Prop _ True `and` Prop _ True = True

or :: Prop -> Prop -> Bool

Prop _ True `or` _             = True
_ `or` Prop _ True             = True
Prop _ False `or` Prop _ False = False

not :: Prop -> Bool

not (Prop _ False) = True
not (Prop _ True)  = False