module Fibonacci.Closed where

open import Level using (0ℓ; _⊔_) 
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Axiom.Extensionality.Propositional
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
open ℤ using (pos; negsuc)
open import Data.Nat as Nat using (ℕ; zero; suc)
import Data.Nat.Coprimality as Coprimality
import Data.Nat.Divisibility as Divisibility


open import Fibonacci.Recursive renaming (fibonacci to fibonacci-recursive)


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


open import Algebra.Field.Extension.BySqrt5
open import Algebra.Field.Exponentiation field-ExtensionBySqrt


-- the ``n``th fibonacci number is
-- ::
--   ((φ ^ n) - ((1 - φ) ^ n)) / sqrt[5]
-- or more concisely with ``φ⁺`` and ``φ⁻``,
-- ::
--   ((φ⁺ ^ n) - (φ⁻ ^ n)) / sqrt[5]
fibonacci-extended : ℕ → ℚ[sqrt[5]]
fibonacci-extended n = ((φ ^ n) - ((1# - φ) ^ n)) ÷′ sqrt[5]|


-- ``fibonacci-extended`` yields an entirely internal, integral, natural result
postulate
  fibonacci-extended-internal : ∀ {n} →
    external (fibonacci-extended n) ≡ 0ℚ
  fibonacci-extended-integral : ∀ {n} →
    ℚ.denominator (internal (fibonacci-extended n)) ≡ pos 0
  fibonacci-extended-natural : ∀ {n} → ∃[ x ]
    (ℚ.numerator (internal (fibonacci-extended n)) ≡ pos x)
    

-- closed formula for the ``n``th Fibonacci number,
-- since ``fibonacci-extended`` yields an entirely internal, natural result
fibonacci : ℕ → ℕ
fibonacci = Int.∣_∣ ∘ ℚ.numerator ∘ internal ∘ fibonacci-extended


-- -- the extended component of ``fibonacci-extended n`` is always ``0ℚ``
-- postulate
--   fibonacci-extended-internal : ∀ n → external (fibonacci-extended n) ≡ 0ℚ


module Fibonacci-Extended-Correct where
  A : Set
  A = ℚ[sqrt[5]]

  open import Algebra.Field.Polynomial field-ExtensionBySqrt _≟′_

  -- nth Fibonacci number (via recursive function)
  F : ℕ → A
  F n = ((mkℚ (pos (fibonacci-recursive n)) 0 isCoprime) +sqrt[5] 0ℚ) where
    isCoprime = Coprimality.sym (Coprimality.1-coprimeTo (fibonacci-recursive n))

  -- f = ∑ F (i+1) * 𝑋ⁱ
  f₀ : PowerSeries
  f₀ = ∑ λ i → F (suc i)

  -- e = ∑[ 2^(i+1) 𝑋ⁱ ]
  e : PowerSeries
  e = ∑ λ i → 2# ^ (suc i)

  -- Observe that ``lim[i→∞] e ≡ 2`` when ``|𝑋| < ½``.
  -- Then since ``0 ≤ f ≤ e``, we also must have that
  -- ``f`` converges when |𝑋| < ½``.

  𝑋*f : PowerSeries
  𝑋*f = 𝑋* f₀

  𝑋^2*f : PowerSeries
  𝑋^2*f = 𝑋²* f₀

  1-𝑋-𝑋² : Polynomial
  1-𝑋-𝑋² = (- 1#) *𝑋^ 2 +ₚ ((- 1#) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ))
  
  -- g₀ = f - 𝑋*f - 𝑋^2*f
  g₀ : PowerSeries
  g₀ = f₀ -ₛ (𝑋*f  -ₛ 𝑋^2*f)

  -- g₁ = (1 - 𝑋 - 𝑋²) * f
  g₁ : PowerSeries
  g₁ = scaleₛ 1-𝑋-𝑋² f₀

  postulate
    g₀≡g₁ : g₀ ≡ g₁

  -- g₂ = F₀*𝑋⁰ + F₁*𝑋¹ + ∑[i≥2] (Fᵢ₊₁ - Fᵢ - Fᵢ₋₁)*𝑋ⁱ
  g₂ : PowerSeries
  g₂ = ∑ a where
    a : ℕ → A
    a 0 = F 1
    a 1 = F 0
    a n@(suc n-1@(suc _)) = F (suc n) - (F n - F n-1)

  postulate
    g₁≡g₂ : g₁ ≡ g₂

  -- g₃ = 1 + 0*𝑋² + ∑[i≥2] 0*𝑋ⁱ
  g₃ : PowerSeries
  g₃ = ∑ a where
    a : ℕ → A
    a 0 = 1#′
    a 1 = 0#′
    a (suc (suc _)) = 0#′

  -- g₄ = 1
  g₄ : Polynomial
  g₄ = 1# *𝑋⁰

  postulate
    g₃⟶∞g₄ : g₃ ⟶∞ g₄

  -- f₁ = (- 𝑋² - 𝑋 + 1)⁻¹
  f₁ : Polynomial
  f₁ = elem ((((- 1#) *𝑋^ 2 +ₚ ((- 1#) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ))) # p) ⁻¹ₚ) where
    postulate
      p : ((-′ (1ℚ +sqrt[α] 0ℚ)) *𝑋^ 2 +ₚ
          ((-′ (1ℚ +sqrt[α] 0ℚ)) *𝑋^ 1 +ₚ
          ((1ℚ +sqrt[α] 0ℚ) *𝑋^ 0 +ₚ 0ₚ)))
          ≉0ₚ

  postulate
    f₀⟶∞f₁ : f₀ ⟶∞ f₁

  -- f₂ = (φ⁺÷(1 + φ⁺𝑋) - φ⁺÷(1 + φ⁺𝑋)) ÷ sqrt[5]
  f₂ : Polynomial
  f₂ = (((φ⁺ *𝑋⁰ ) ÷ₚ ((φ⁺ *𝑋^ 1 +ₚ 1ₚ) # p₁)) -ₚ
       (((φ⁻ *𝑋⁰ ) ÷ₚ ((φ⁻ *𝑋^ 1 +ₚ 1ₚ) # p₂)))) ÷ₚ
       ((sqrt[5] *𝑋⁰) # p₃) where
    postulate
      p₁ : (φ⁺ *𝑋^ 1 +ₚ ((1ℚ +sqrt[α] 0ℚ) *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ
      p₂ : (φ⁻ *𝑋^ 1 +ₚ ((1ℚ +sqrt[α] 0ℚ) *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ
      p₃ : (sqrt[5] *𝑋^ 0 +ₚ 0ₚ) ≉0ₚ

  postulate
    f₁≡f₂ : f₁ ≡ f₂

  -- f₃ = (φ⁺ ∑ (φ⁺ 𝑋)ⁱ - φ⁻ ∑ (φ⁻ 𝑋)ⁱ) ÷ sqrt[5]
  f₃ : PowerSeries
  f₃ = scaleₛ (sqrt[5]⁻¹ *𝑋⁰)
         ((scaleₛ (φ⁺ *𝑋⁰) (∑ (λ i → φ⁺ ^ i))) -ₛ
          (scaleₛ (φ⁻ *𝑋⁰) (∑ (λ i → φ⁻ ^ i))))

  postulate
    f₂∞⟵f₃ : f₃ ⟶∞ f₂

  -- hᵢ = ((φ⁺)ⁱ⁺¹ - (φ⁻)ⁱ⁺¹) ÷ sqrt[5]
  -- hᵢ = ((φ⁺)ⁱ - (φ⁻)ⁱ) ÷ sqrt[5]
  h : ℕ → A
  h = fibonacci-extended
  --= ((φ⁺ ^ suc i) - (φ⁻ ^ suc i)) ÷ sqrt[5]|

  -- f₄ = ∑ ((φ⁺)ⁱ⁺¹ - (φ⁻)ⁱ⁺¹) ÷ sqrt[5]
  f₄ : PowerSeries
  f₄ = ∑ λ i → h (suc i)

  postulate
    f₃≡f₄ : f₃ ≡ f₄

  postulate
    f₀≡f₃ : f₀ ≡ f₃

  Fₙ≡hₙ : ∀ {n} → F n ≡ h n
  Fₙ≡hₙ {n} = ps-≡-suc {F} {h}
    (begin
      f₀ ≡⟨ f₀≡f₃ ⟩
      f₃ ≡⟨ f₃≡f₄ ⟩
      f₄
    ∎) {n} 
    where open ≡-Reasoning
