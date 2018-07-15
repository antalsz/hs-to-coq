{-# OPTIONS_GHC -fplugin=HsToCoq.Plugin #-}

module Fib where

fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n - 2) + fib (n - 1)
