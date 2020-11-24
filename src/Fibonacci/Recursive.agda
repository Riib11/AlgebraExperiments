open import Data.Nat

module Fibonacci.Recursive where

-- recursive formula for the ``n``th Fibonacci number
fibonacci : ℕ → ℕ
fibonacci 0             = 0
fibonacci (suc 0)       = suc 0
fibonacci (suc (suc n)) = fibonacci (suc n) + fibonacci n
