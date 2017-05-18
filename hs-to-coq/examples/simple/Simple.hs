import Prelude (Bool(..), otherwise, Show)

--data Maybe a = Nothing | Just a deriving Show
type Option = Maybe -- For ML programmers

data Weekday = Monday   | Tuesday | Wednesday | Thursday | Friday
             | Saturday | Sunday
             deriving Show

isWeekend :: Weekday -> Bool
isWeekend Saturday = True
isWeekend Sunday   = True
isWeekend _        = False

lazyApply :: Weekday -> (a -> b) -> a -> Maybe b
lazyApply day f x | isWeekend day = Nothing -- nah
                  | otherwise     = Just (f x)

not :: Bool -> Bool
not True  = False
not False = True

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs
