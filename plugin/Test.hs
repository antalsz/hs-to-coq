{-# OPTIONS_GHC -fplugin GHC.Proof.Plugin #-}

module Test where

fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n - 2) + fib (n - 1)
