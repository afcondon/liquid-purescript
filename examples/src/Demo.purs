module Demo where

import Prelude

abs :: Int -> Int
abs n = if n > 0 then n else 0 - n

bad :: Int -> Int
bad n = n - 1

clamp :: Int -> Int -> Int -> Int
clamp lo hi x = if x < lo then lo else if x > hi then hi else x

sign :: Int -> Int
sign n
  | n > 0 = 1
  | n < 0 = 0 - 1
  | otherwise = 0

double :: Int -> Int
double n = let m = n + n in m

low :: Int -> Int
low n = min n 0

flag :: Int -> Boolean
flag n = n >= 0

once :: Int -> Int
once n = n
