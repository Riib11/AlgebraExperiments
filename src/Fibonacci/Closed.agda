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
open import Algebra.Structures

open import Data.Subset
open import Algebra.Field
import Algebra.Field.Rational as FieldRat

open import Data.Rational as Rat using (ℚ; mkℚ; 0ℚ; 1ℚ; ½)
open import Data.Integer as Int using (ℤ)
open ℤ using (pos; negsuc)
open import Data.Nat as Nat using (ℕ; zero) renaming (suc to _+1)
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
--   fibonacci-rec (1+ (n +1)) = ficonacci-rec (n +1) + fibonacci-rec n
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
fibonacci-extended n = ((φ⁺ ^ n) - (φ⁻ ^ n)) ÷′ sqrt[5]|

-- some example values

_ : fibonacci-extended 0 ≡ 0#
_ = refl
_ : fibonacci-extended 1 ≡ 1#
_ = refl
_ : fibonacci-extended 2 ≡ 1#
_ = refl
_ : fibonacci-extended 3 ≡ 2#
_ = refl
_ : fibonacci-extended 4 ≡ 3#
_ = refl
_ : fibonacci-extended 5 ≡ 5#
_ = refl


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


module Correct where
  -- alias for commonly used domain
  A : Set
  A = ℚ[sqrt[5]]

  -- some useful constants

  4ℚ : ℚ
  4ℚ = 1ℚ Rat.+ 1ℚ Rat.+ 1ℚ Rat.+ 1ℚ

  -- 4# : ℚ[sqrt[5]]
  -- 4# = 4ℚ +sqrt[5] 0ℚ

  ¼ℚ : ℚ
  ¼ℚ = mkℚ (pos 1) 3 coprime-1-4 where
    coprime-1-4 = Coprimality.1-coprimeTo 4

  ¼# : ℚ[sqrt[5]]
  ¼# = ¼ℚ +sqrt[5] 0ℚ

  open import Algebra.Field.PolynomialNew field-ExtensionBySqrt ¼#

  -- nth Fibonacci number (via recursive function) in ℚ[Sqrt[5]]
  F : ℕ → A
  F 0 = 0#
  F 1 = 1#
  F ((n +1) +1) = F (n +1) + F n

  -- f = ∑ F (i+1) * 𝑋ⁱ
  f₀ : PowerSeries
  f₀ = ∑ λ i → F (i +1)

  -- e = ∑[ 2^(i+1) 𝑋ⁱ ]
  e : PowerSeries
  e = ∑ λ i → 2# ^ (i +1)

  -- Observe that ``lim[i→∞] e ≡ 2`` (since ``|𝑋| = ¼ < ½``).
  -- Since ``0 ≤ f ≤ e``, we must also have that ``f`` converges.

  𝑋*f₀ : PowerSeries
  𝑋*f₀ = 𝑋* f₀

  𝑋^2*f₀ : PowerSeries
  𝑋^2*f₀ = 𝑋²* f₀

  1-𝑋-𝑋² : Polynomial
  1-𝑋-𝑋² = -1# *𝑋^ 2 +ₚ (-1# *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ))
  
  -- g₀ = f₀ - 𝑋*f₀ - 𝑋^2*f₀
  g₀ : PowerSeries
  g₀ = f₀ -ₛ (𝑋*f₀  +ₛ 𝑋^2*f₀)

  -- g₁ = (1 - 𝑋 - 𝑋²) * f₀
  g₁ : PowerSeries
  g₁ = scaleₛ 1-𝑋-𝑋² f₀

  postulate
    n-n≡0 : ∀ n → n - n ≡ 0#
    -n+n≡0 : ∀ n → (- n) + n ≡ 0#
    0≡-n+n : ∀ n → 0# ≡ (- n) + n
    n-0≡0 : ∀ n → n - 0# ≡ 0#
    n+0≡0 : ∀ n → n + 0# ≡ 0#
    n≡n+0 : ∀ n → n ≡ n + 0#
    -n≡-1*n : ∀ n → (- n) ≡ -1# * n
    n≡1*n : ∀ n → n ≡ 1# * n
    +-comm : ∀ m n → m + n ≡ n + m
    +-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
    *-distribˡ : ∀ l m n → l * (m + n) ≡ (l * m) + (l * n)

  -- postulate
  --   g₀≈ₛg₁ : g₀ ≈ₛ g₁
  g₀≈ₛg₁ : g₀ ≈ₛ g₁
  g₀≈ₛg₁ 0 rewrite n-0≡0 0# = refl
  g₀≈ₛg₁ 1 rewrite n+0≡0 1# = refl
  g₀≈ₛg₁ (1+ (i +1)) =
    begin

      ((F₁ + F₀) + F₁) - ((F₁ + F₀) + F₁)

    ≡⟨ n-n≡0 ((F₁ + F₀) + F₁) ⟩

      0#

    ≡⟨ 0≡-n+n (F₁ + (F₁ + F₀)) ⟩

      ((- (F₁ + (F₁ + F₀))) + (F₁ + (F₁ + F₀)))

    ≡⟨ cong (λ a → (- (F₁ + (F₁ + F₀))) + (F₁ + a)) (+-comm F₁ F₀) ⟩

      ((- (F₁ + (F₁ + F₀))) + (F₁ + (F₀ + F₁)))

    ≡⟨ cong (λ a → (- (F₁ + (F₁ + F₀))) + a)

      (sym (+-assoc F₁ F₀ F₁)) ⟩ ((- (F₁ + (F₁ + F₀))) + ((F₁ + F₀) + F₁))
      
    ≡⟨ cong (λ a → (a + ((F₁ + F₀) + F₁))) (-n≡-1*n (F₁ + (F₁ + F₀))) ⟩

      ((-1# * (F₁ + (F₁ + F₀))) + ((F₁ + F₀) + F₁))
      
    ≡⟨ cong (λ a → ((-1# * (F₁ + (F₁ + F₀))) + a)) (n≡1*n ((F₁ + F₀) + F₁)) ⟩

      ((-1# * (F₁ + (F₁ + F₀))) + (1# *′ ((F₁ + F₀) + F₁)))
      
    ≡⟨ cong (λ a → a + (1# *′ ((F₁ + F₀) + F₁))) (*-distribˡ -1# F₁ (F₁ + F₀)) ⟩

      (((-1# *′ F₁) + (-1# *′ (F₁ + F₀))) +  (1# *′ ((F₁ + F₀) + F₁)))

    ≡⟨ +-assoc (-1# *′ F₁) (-1# *′ (F₁ + F₀)) (1# *′ ((F₁ + F₀) + F₁)) ⟩

      ( (-1# *′ F₁) + ((-1# *′ (F₁ + F₀))  +  (1# *′ ((F₁ + F₀) + F₁))))

    ≡⟨ cong (λ a → ((-1# *′ F₁) + ((-1# *′ (F₁ + F₀)) + a))) (n≡n+0 (1# *′ ((F₁ +′ F₀) +′ F₁))) ⟩

      ( (-1# *′ F₁) + ((-1# *′ (F₁ + F₀))  + ((1# *′ ((F₁ + F₀) + F₁)) + 0#)))

    ∎
    where
      F₀ = F i
      F₁ = F (i +1)
      open ≡-Reasoning

  -- g₂ = F₀*𝑋⁰ + F₁*𝑋¹ + ∑[i≥2] (Fᵢ₊₁ - Fᵢ - Fᵢ₋₁)*𝑋ⁱ
  g₂ : PowerSeries
  g₂ = ∑ a where
    a : ℕ → A
    a 0 = F 1
    a 1 = F 0
    a i@(i-1@(_ +1) +1) = F (i +1) - (F i - F i-1)

  postulate
    g₁≈g₂ : g₁ ≈ₛ g₂

  -- g₃ = 1 + 0*𝑋² + ∑[i≥2] 0*𝑋ⁱ
  g₃ : PowerSeries
  g₃ = ∑ a where
    a : ℕ → A
    a 0 = 1#
    a 1 = 0#
    a ((_ +1) +1) = 0#′

  -- g₄ = 1
  g₄ : Polynomial
  g₄ = 1# *𝑋⁰

  postulate
    g₃⟶∞g₄ : g₃ ⟶∞ g₄

  -- f₁ = (- 𝑋² - 𝑋 + 1)⁻¹
  f₁ : Polynomial
  f₁ = elem ((((- 1#) *𝑋^ 2 +ₚ ((- 1#) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ))) # p) ⁻¹ₚ) where
    postulate
      p : ((- 1#) *𝑋^ 2 +ₚ ((- 1#) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ))) ≉0ₚ

  postulate
    f₀⟶∞f₁ : f₀ ⟶∞ f₁

  limit[f₀]≡f₁ : limit f₀ f₀⟶∞f₁ ≡ f₁
  limit[f₀]≡f₁ = refl
  

  -- f₂ = (φ⁺÷(1 + φ⁺𝑋) - φ⁺÷(1 + φ⁺𝑋)) ÷ sqrt[5]
  f₂ : Polynomial
  f₂ = (((φ⁺ *𝑋⁰ ) ÷ₚ ((φ⁺ *𝑋^ 1 +ₚ 1ₚ) # p₁)) -ₚ
       (((φ⁻ *𝑋⁰ ) ÷ₚ ((φ⁻ *𝑋^ 1 +ₚ 1ₚ) # p₂)))) ÷ₚ
       ((sqrt[5] *𝑋⁰) # p₃) where
    postulate
      p₁ : (φ⁺ *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ
      p₂ : (φ⁻ *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ
      p₃ : (sqrt[5] *𝑋^ 0 +ₚ 0ₚ) ≉0ₚ

  postulate
    f₁≈f₂ : f₁ ≈ₚ f₂

  -- f₃ = (φ⁺ ∑ (φ⁺ 𝑋)ⁱ - φ⁻ ∑ (φ⁻ 𝑋)ⁱ) ÷ sqrt[5]
  f₃ : PowerSeries
  f₃ = scaleₛ (sqrt[5]⁻¹ *𝑋⁰)
         ((scaleₛ (φ⁺ *𝑋⁰) (∑ (λ i → φ⁺ ^ i))) -ₛ
          (scaleₛ (φ⁻ *𝑋⁰) (∑ (λ i → φ⁻ ^ i))))

  postulate
    f₂∞⟵f₃ : f₃ ⟶∞ f₂

  limit[f₃]≡f₂ : limit f₃ f₂∞⟵f₃ ≡ f₂
  limit[f₃]≡f₂ = refl

  limit[f₀]≈ₚlimit[f₃] : limit f₀ f₀⟶∞f₁ ≈ₚ limit f₃ f₂∞⟵f₃
  limit[f₀]≈ₚlimit[f₃] = f₁≈f₂

  -- hᵢ = ((φ⁺)ⁱ⁺¹ - (φ⁻)ⁱ⁺¹) ÷ sqrt[5]
  h : ℕ → A
  h = fibonacci-extended
  
  -- f₄ = ∑ ((φ⁺)ⁱ⁺¹ - (φ⁻)ⁱ⁺¹) ÷ sqrt[5]
  f₄ : PowerSeries
  f₄ = ∑ λ i → h (i +1)

  postulate
    f₃≈f₄ : f₃ ≈ₛ f₄

  f₀≈f₃ : f₀ ≈ₛ f₃
  f₀≈f₃ = limit-injective f₀ f₀⟶∞f₁ f₃ f₂∞⟵f₃ limit[f₀]≈ₚlimit[f₃]

  f₀≈f₄ : f₀ ≈ₛ f₄
  f₀≈f₄ = IsEquivalence.trans ≈ₛ-isEquivalence f₀≈f₃ f₃≈f₄

  Fₙ₊₁≡hₙ₊₁ : ∀ {n} → F (n +1) ≡ h (n +1)
  Fₙ₊₁≡hₙ₊₁ {n} = f₀≈f₄ n

  Fₙ≡hₙ : ∀ {n} → F n ≡ h n
  Fₙ≡hₙ {zero} = refl
  Fₙ≡hₙ {n +1} = Fₙ₊₁≡hₙ₊₁

  
