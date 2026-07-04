module P2 where

import Prelude

data IntList = INil | ICons Int IntList

count :: IntList -> Int
count l = case l of
  INil -> 0
  ICons _ t -> 1 + count t

append :: IntList -> IntList -> IntList
append a b = case a of
  INil -> b
  ICons h t -> ICons h (append t b)

-- forgets the +1: cannot equal the measure
badCount :: IntList -> Int
badCount l = case l of
  INil -> 0
  ICons _ t -> badCount t

singleton :: Int -> IntList
singleton x = ICons x INil

-- total head: the precondition rules INil out
headOr :: IntList -> Int
headOr l = case l of
  ICons h _ -> h
  INil -> 0
