module Arrays where

import Prelude

import Data.Array (cons, drop, length, take)

three :: Array Int
three = [ 1, 2, 3 ]

grow :: Array Int -> Array Int
grow xs = cons 0 xs

mid :: Array Int -> Int
mid xs = length xs / 2

-- same body, no non-empty precondition: mid [] = 0 is not < length []
badMid :: Array Int -> Int
badMid xs = length xs / 2

firstHalf :: Array Int -> Array Int
firstHalf xs = take (length xs / 2) xs

rest :: Array Int -> Array Int
rest xs = drop 1 xs
