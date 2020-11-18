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

open import Subset
open import StructureField
open import FieldRational

open import Data.Rational as Rat hiding (_+_; _*_)
import Data.Integer as Int
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
-- constant. Each recursive call spawns 2 further calls, and the max call depth
-- is ``n``, so the resulting binary recursion-tree has height ``n``
-- (though all but one of the paths from root to leaf have length less than ``n``).
-- For a binary tree of height ``n``, the number of nodes in the tree
-- is less than ``2^n``. So, the time complexity of ``fibonacci-rec``
-- is ``O(log[2^n])``. We can show a slighter tighter bound, however.

-- ----------------------------------------------------------------
-- Fibonacci via Closed Formula over ℚ[sqrt[5]]
-- ----------------------------------------------------------------
-- This module's implementation instead uses the closed formula
-- ::
--   fibonacci-ext n = φ ^ n - (1 - φ) ^ n
-- where ``φ = (1/2)(1 + sqrt[5])`` (the golden ratio).
-- Given constant-time addition and multiplication, this formula
-- computes with the complexity of raising ``φ`` to the power ``n``,
-- which via simply-recursive exponentiation is ``O(n)``.


5ℚ : ℚ
5ℚ = mkℚ (Int.+ 5) 0 coprime-5-1 where
  coprime-5-1 : Coprimality.Coprime 5 1
  coprime-5-1 = Divisibility.∣1⇒≡1 ∘ proj₂

open import AlgebraicFieldExtension _≡_ 5ℚ
open IsField-AlgebraicExtensionBySqrt 0ℚ 1ℚ Rat._+_ Rat._*_ -_ _⁻¹ isField-ℚ


-- the rationals extended by ``sqrt[5]``
ℚ[sqrt[5]] : Set
ℚ[sqrt[5]] = AlgebraicFieldExtensionBySqrt


-- extended constants
sqrt[5] : ℚ[sqrt[5]]
sqrt[5] = 0ℚ +sqrt[α] 1ℚ
-- the golden ratio
φ : ℚ[sqrt[5]]
φ = ½ +sqrt[α] ½


module _ where
  open Nat hiding (_^_)
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



-- the ``n``th fibonacci number is ``φ ^ n - (1 - φ) ^ n``
fibonacci-extended : ℕ → ℚ[sqrt[5]]
fibonacci-extended n = (φ ^ n) -′ ((1#′ -′ φ) ^ n) where
  open IsField isField-AlgebraicExtensionBySqrt


-- the extended component of ``fibonacci-extended n`` is always ``0ℚ``
postulate
  fibonacci-extended-internal : ∀ n → external (fibonacci-extended n) ≡ 0ℚ


-- closed formula for the ``n``th Fibonacci number
fibonacci : ℕ → ℕ
fibonacci = Int.∣_∣ ∘ Rat.ℚ.numerator ∘ internal ∘ fibonacci-extended


-- recursive formula for the ``n``th Fibonacci number
fibonacci-rec : ℕ → ℕ
fibonacci-rec 0 = 0
fibonacci-rec (suc 0) = suc 0
fibonacci-rec (suc (suc n)) = fibonacci-rec (suc n) Nat.+ fibonacci-rec n


-- closed formula and recursive formula always yield same answer
postulate
  fibonacci-correct : ∀ n → fibonacci n ≡ fibonacci-rec n
