import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Algebra.Field
open import Algebra.Core
open import Data.Subset
open import Data.Product
open import Data.Nat as Nat using (ℕ; suc; zero; _⊔_)
open import Data.Fin as Fin using (Fin)

module Algebra.Field.Polynomial {a ℓ} (F : Field a ℓ)
  (_≟_ : Decidable (Field._≈_ F))
  where

open Field F renaming (Carrier to A)
open import Algebra.Field.Exponentiation F


data Polynomial : Set a where
  0ₚ : Polynomial
  _*𝑋^_+ₚ_ : A → ℕ → Polynomial → Polynomial

_*𝑋⁰ : A → Polynomial
a *𝑋⁰ = a *𝑋^ 0 +ₚ 0ₚ

1ₚ : Polynomial
1ₚ = 1# *𝑋⁰

postulate
  _≈ₚ_ : Rel Polynomial ℓ
  _≉ₚ_ : Rel Polynomial ℓ
  _≉0ₚ : Polynomial → Set ℓ

Polynomial≉0ₚ : Set (a Level.⊔ ℓ)
Polynomial≉0ₚ = Subset Polynomial _≉0ₚ

postulate
  _≟ₚ_ : Decidable _≈ₚ_
  _+ₚ_ : Op₂ Polynomial
  _-ₚ_ : Op₂ Polynomial
  _*ₚ_ : Op₂ Polynomial
  scaleₚ : A → Polynomial → Polynomial
  _⁻¹ₚ : Op₁ Polynomial≉0ₚ
  _÷ₚ_ : Polynomial → Polynomial≉0ₚ → Polynomial

-- -- TODO: review this requirement, maybe move to convergence axioms
-- -- require that |𝑋| < ½,
-- -- which is used in convergence axioms
-- data Polynomial : ℕ → Set (a Level.⊔ ℓ) where
--   0ₚ : Polynomial 0
--   _*𝑋^[1+_]+ₚ_ : A≉0# → ∀ n → Polynomial n → Polynomial (suc n)

-- _ : Polynomial 1
-- _ = 1#| *𝑋^[1+ 0 ]+ₚ 0ₚ

-- postulate
--   _+ₚ_ : ∀ {m n} → Polynomial m → Polynomial n → Polynomial (m ⊔ n)
-- 0ₚ +ₚ 0ₚ = 0ₚ
-- 0ₚ +ₚ (x *𝑋^[1+ n ]+ₚ q) = x *𝑋^[1+ n ]+ₚ q
-- (x *𝑋^[1+ n ]+ₚ p) +ₚ 0ₚ = x *𝑋^[1+ n ]+ₚ p
-- ((x # _) *𝑋^[1+ n ]+ₚ p) +ₚ ((y # _) *𝑋^[1+ m ]+ₚ q)
--   with n Nat.≟ m
-- ...  | yes _ with (x + y) ≟ 0#
-- ...             | yes _ = p +ₚ q
-- ...             | no  _ = {!!}
-- ...  | no  _ = {!!}

-- polynomials inherit decidable equivalence from underlying set

-- _≟ₚ_ : Decidable {A = ∀ {n} → Polynomial n} _≡_
-- 0ₚ ≟ₚ 0ₚ = yes refl
-- ((a # pa) *𝑋^[1+ n ]+ₚ p) ≟ₚ ((b # pb) *𝑋^[1+ .n ]+ₚ q)
--   with a ≟ b
-- ... | yes _ = {!p ≟ₚ q!}
-- ... | no  _ = {!!}
-- (a|@(a # pa) *𝑋^[1+ n ]+ₚ p) ≟ₚ (b|@(b # pb) *𝑋^[1+ .n ]+ₚ q)
--    with a ≟ b | p ≟ₚ q
-- ...  | yes a≡b | yes p≡q rewrite a≡b | p≡q
--                          = yes refl
-- ...  | yes a≡b | no ¬p≡q = no λ { refl → ¬p≡q refl }
-- ...  | no ¬a≡b | _       = no λ { refl → ¬a≡b refl }


-- power series
data PowerSeries : Set (a Level.⊔ ℓ) where
  -- ∑[ aᵢ xⁱ ]
  ∑_ : (ℕ → A) → PowerSeries

partial-∑ : PowerSeries → ℕ → Polynomial
partial-∑ (∑ a-) zero = 0ₚ
partial-∑ (∑ a-) (suc n) = a- n *𝑋^ n +ₚ partial-∑ (∑ a-) n

0∑ : PowerSeries
0∑ = ∑ λ _ → 0#

-- 𝑋 * ∑ a- 𝑋ⁱ = ∑ a- 𝑋ⁱ⁺¹
𝑋*_ : Op₁ PowerSeries
𝑋* (∑ a-) = ∑ (λ i → a- (suc i))

-- 𝑋ⁿ * ∑ a- 𝑋ⁱ = ∑[i≥n] a- 𝑋ⁱ
𝑋^[_]*_ : ℕ → PowerSeries → PowerSeries
𝑋^[ zero ]* (∑ a) = ∑ a
𝑋^[ suc n ]* (∑ a) = 𝑋* (𝑋^[ n ]* (∑ a))

𝑋²*_ : Op₁ PowerSeries
𝑋²*_ = 𝑋*_ ∘ 𝑋*_

_+ₛ_ : Op₂ PowerSeries
(∑ a-) +ₛ (∑ b-) = ∑ (λ i → a- i + b- i)

_-ₛ_ : Op₂ PowerSeries
(∑ a-) -ₛ (∑ b-) = ∑ (λ i → a- i - b- i)

scaleₛ : Polynomial → PowerSeries → PowerSeries
scaleₛ 0ₚ (∑ a-) = 0∑
scaleₛ (a *𝑋^ n +ₚ p) (∑ b-) = 𝑋^[ n ]* (scaleₛ p (∑ (λ i → a * b- i)))


private
  postulate
    A1 : ∀ {a| : A≉0#} → ((- elem a|) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ

data _⟶∞_ : PowerSeries → Polynomial → Set (a Level.⊔ ℓ) where
  -- ∑ (a𝑋)ⁱ ⟶∞ (1 - a𝑋)⁻¹, for |𝑋| < ½
  converge1 : ∀ (a|@(a # pa) : A≉0#) →
    (∑ λ i → a ^ i) ⟶∞
    elem ((((- a) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)) # A1 {a|}) ⁻¹ₚ)


limit : ∀ P {p} → .(P ⟶∞ p) → Polynomial
limit P {p} ._ = p

-- useful lemmas about power series
postulate
  ps-≡ : ∀ {a b} → ∑ a ≡ ∑ b → ∀ {i} → a i ≡ b i
  ps-≡-suc : ∀ {a b : ℕ → A} → (∑ λ i → a (suc i)) ≡ (∑ λ i → b (suc i)) → ∀ {i} → a i ≡ b i
