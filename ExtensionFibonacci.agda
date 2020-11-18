module ExtensionFibonacci where

open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Unit

open import Algebra.Core

open import Data.Subset
open import Algebra.Field
import Algebra.Field.Rational as FieldRat

open import Data.Rational as Rat using (ℚ; mkℚ; 0ℚ; 1ℚ; ½)
open import Data.Integer as Int using (ℤ)
open import Data.Nat as Nat using (ℕ; zero; suc)
import Data.Nat.Coprimality as Coprimality
import Data.Nat.Divisibility as Divisibility

-- ================================================================
-- Extension Fibonacci
-- ================================================================
-- This module implements a function ``fibonacci : (n : ℕ) → ℕ``
-- which computes the ``n``th Fibonacci number using the closed formula.

-- ----------------------------------------------------------------
-- Fibonacci via Recursive Formula
-- ----------------------------------------------------------------
-- A common implementation of this is the following recursive function:
-- ::
--   fibonacci-rec 0 = 0
--   fibonacci-rec 1 = 1
--   fibonacci-rec (suc (suc n)) = ficonacci-rec (suc n) + fibonacci-rec n
-- For the sake of simplicity, assume we are working with fixed-size
-- numerical representations, so that addition and multiplication are
-- constant-time. Each recursive call spawns 2 further calls, and
-- the max call depth is ``n``, so the resulting binary recursion-tree has height ``n``
-- (though all but one of the root-to-leaf-paths have length less than ``n``).
-- For a binary tree of height ``n``, the number of nodes in the tree
-- is less than ``2^n``. So, the time complexity of ``fibonacci-rec``
-- is ``O(log[2^n])``.

-- ----------------------------------------------------------------
-- Fibonacci via Closed Formula over ℚ[sqrt[5]]
-- ----------------------------------------------------------------
-- This module's implementation instead uses the closed formula
-- ::
--   fibonacci-ext n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]
-- where ``φ = (1/2)(1 + sqrt[5])`` (the golden ratio).
-- For the sake of simplicity, assume we are working with fixed-size
-- numerical representations, so that addition, multiplication, and
-- inversion are constant-time. Then this formula computes with
-- the complexity of raising ``φ`` to the power ``n``,
-- which via recursive exponentiation involves ``n`` multiplications
-- and so is ``O(n)``.


5ℚ : ℚ
5ℚ = mkℚ (Int.+ 5) 0 coprime-5-1 where
  coprime-5-1 : Coprimality.Coprime 5 1
  coprime-5-1 = Divisibility.∣1⇒≡1 ∘ proj₂


open import Algebra.Field.Extension.BySqrt _≡_ 5ℚ as Extension
open Extension.IsField-ExtensionBySqrt 0ℚ 1ℚ Rat._+_ Rat._*_ Rat.-_ FieldRat._⁻¹ FieldRat.isField-ℚ


-- the rationals extended by ``sqrt[5]``
ℚ[sqrt[5]] : Set
ℚ[sqrt[5]] = Extension.BySqrt

_+sqrt[5]_ : ℚ → ℚ → ℚ[sqrt[5]]
a +sqrt[5] b = a +sqrt[α] b


-- extended constants
sqrt[5] : ℚ[sqrt[5]]
sqrt[5] = 0ℚ +sqrt[5] 1ℚ
-- the golden ratio
φ : ℚ[sqrt[5]]
φ = ½ +sqrt[5] ½


module _ where
  open Nat using (_+_)
  open import Data.Nat.Properties

  -- linear exponentiation
  _^_ : ℚ[sqrt[5]] → ℕ → ℚ[sqrt[5]]
  x ^ 0 = 1#′
  x ^ suc n = x *′ (x ^ n)
                                          
  ⌊_/2⌋-remainder : (n : ℕ) → ∃[ n′ ] ((n ≡ n′ + n′) ⊎ (n ≡ suc (n′ + n′)))
  ⌊ 0 /2⌋-remainder = 0 , (inj₁ refl)
  ⌊ suc n /2⌋-remainder with ⌊ n /2⌋-remainder
  ... | n′ , inj₁ n≡2n′ rewrite n≡2n′ = n′ , inj₂ refl
  ... | n′ , inj₂ n≡s2n′ rewrite n≡s2n′ | sym (+-suc n′ n′) = suc n′ , inj₁ refl

  -- for fun, this is exponentiation via repeated squaring;
  -- using binary representations, this can slightly speed up exponentiation
  -- x ^₂ (2 * n) = (x ^₂ n) * (x ^₂ n)
  {-# TERMINATING #-} -- since n′ < n
  _^₂_ : ℚ[sqrt[5]] → ℕ → ℚ[sqrt[5]]
  x ^₂ 0 = 1#′
  x ^₂ n@(suc _) with ⌊ n /2⌋-remainder
  ... | n′ , inj₁ n≡2n′   = (x ^₂ n′) *′ (x ^₂ n′) 
  ... | n′ , inj₂ n≡2n′+1 = ((x ^₂ n′) *′ (x ^₂ n′)) *′ x

  postulate
    ^₂-correct : ∀ x n → x ^ n ≡ x ^₂ n

  -- example: correct for ``2 ^ 10``
  #2′ : ℚ[sqrt[5]]
  #2′ = 1#′ +′ 1#′
  _ : #2′ ^ 10 ≡ #2′ ^₂ 10
  _ = refl



-- the ``n``th fibonacci number is ``((φ ^ n) - ((1 - φ) ^ n)) / sqrt[5]``
fibonacci-extended : ℕ → ℚ[sqrt[5]]
fibonacci-extended n = ((φ ^ n) -′ ((1#′ -′ φ) ^ n)) *′ elem (sqrt[5]N ⁻¹′)
  where
    open IsField isField-ExtensionBySqrt
    sqrt[5]N = sqrt[5] # (λ ())
    

-- the extended component of ``fibonacci-extended n`` is always ``0ℚ``
postulate
  fibonacci-extended-internal : ∀ n → external (fibonacci-extended n) ≡ 0ℚ


-- closed formula for the ``n``th Fibonacci number
fibonacci : ℕ → ℕ
fibonacci = Int.∣_∣ ∘ ℚ.numerator ∘ internal ∘ fibonacci-extended


-- recursive formula for the ``n``th Fibonacci number
fibonacci-rec : ℕ → ℕ
fibonacci-rec 0 = 0
fibonacci-rec (suc 0) = suc 0
fibonacci-rec (suc (suc n)) = fibonacci-rec (suc n) Nat.+ fibonacci-rec n


-- closed formula and recursive formula always yield same answer
postulate
  fibonacci-correct : ∀ n → fibonacci n ≡ fibonacci-rec n
