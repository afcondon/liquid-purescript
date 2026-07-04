module P1 where

import Prelude

myAbs :: Int -> Int
myAbs n = if n > 0 then n else 0 - n

dist :: Int -> Int -> Int
dist x y = myAbs (x - y)

sumTo :: Int -> Int
sumTo n = if n <= 0 then 0 else n + sumTo (n - 1)

inc :: Int -> Int
inc n = n + 1

callGood :: Int -> Int
callGood n = inc (myAbs n)

callBad :: Int -> Int
callBad n = inc n

low2 :: Int -> Int
low2 n = min n 0

size :: Int -> Int
size n = case n of
  0 -> 0
  1 -> 1
  _ -> 2
