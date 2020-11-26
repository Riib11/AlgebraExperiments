open import Level using (0ℓ)
open import Relation.Binary

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Nat.Coprimality as Coprimality
open import Data.Nat.Divisibility as Divisibility
open import Data.Integer as Int using (ℤ)
open import Data.Rational as Rat using (ℚ; mkℚ; 0ℚ; 1ℚ; ½)
open import Data.Subset


open import Algebra.Core
open import Algebra.Structures
import Algebra.Field.Rational as RatField


module Algebra.Field.Extension.BySqrt5 where


open import Algebra.Field using (Field)


5ℚ : ℚ
5ℚ = mkℚ (Int.+ 5) 0 coprime-5-1 where
  coprime-5-1 : Coprime 5 1
  coprime-5-1 = ∣1⇒≡1 ∘ proj₂

postulate
  5-squarefree : ¬ ∃[ r ] ((r Rat.* r) ≡ 5ℚ)


open import Algebra.Field.Extension.BySqrt _≡_ 5ℚ as ExtensionBySqrt public
  
open IsField-E
  0ℚ
  1ℚ
  Rat._+_
  Rat._*_
  Rat.-_
  RatField._⁻¹
  5-squarefree
  RatField.isField-ℚ
  public


open Field field-E public

-- the rationals extended by ``sqrt[5]``
ℚ[sqrt[5]] : Set
ℚ[sqrt[5]] = E

_+sqrt[5]_ : ℚ → ℚ → ℚ[sqrt[5]]
a +sqrt[5] b = a +sqrt[α] b


-- some extended constants

sqrt[5] : ℚ[sqrt[5]]
sqrt[5] = 0ℚ +sqrt[5] 1ℚ

sqrt[5]| : E≉0#′
sqrt[5]| = sqrt[5] # (λ ())

sqrt[5]⁻¹ : ℚ[sqrt[5]]
sqrt[5]⁻¹ = 1# ÷ sqrt[5]|

-- the golden ratio
φ : ℚ[sqrt[5]]
φ = ½ +sqrt[5] ½

φ⁺ : ℚ[sqrt[5]]
φ⁺ = φ

φ⁻ : ℚ[sqrt[5]]
φ⁻ = ½ +sqrt[5] (Rat.- ½)


-- useful derivatives

_≟′_ : Decidable _≈′_
(r +sqrt[α] s) ≟′ (t +sqrt[α] u)
  with r Rat.≟ t | s Rat.≟ u
... | yes r≡t | yes s≡u rewrite r≡t | s≡u = yes (refl , refl)
... | yes r≡t | no ¬s≡u = no λ { (_   , s≡u) → ¬s≡u s≡u }
... | no ¬r≡t | yes s≡u = no λ { (r≡t , _  ) → ¬r≡t r≡t }
... | no ¬r≡t | no ¬s≡u = no λ { (r≡t , s≡u) → ¬s≡u s≡u }

