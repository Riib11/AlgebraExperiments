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

module Algebra.Field.Polynomial {a ℓ} (F : Field a ℓ)
  (𝑥 : Field.Carrier F) -- value of ``𝑋``
  where

open Field F renaming (Carrier to A)
open import Algebra.Field.Exponentiation F


-- Polynomials in ``𝑋``
-- We use this particular value for the purposes
-- of reasoning about convergent limitss
data Polynomial : Set a where
  0ₚ : Polynomial
  _*𝑋^_+ₚ_ : A → ℕ → Polynomial → Polynomial

_*𝑋⁰ : A → Polynomial
a *𝑋⁰ = a *𝑋^ 0 +ₚ 0ₚ

1ₚ : Polynomial
1ₚ = 1# *𝑋⁰

-- substitute ``𝑥`` for ``𝑋`` in the ``p``
⟦_⟧ : Polynomial → A
⟦ 0ₚ ⟧ = 0#
⟦ a *𝑋^ n +ₚ p ⟧ = (a * (𝑥 ^ n)) + ⟦ p ⟧

-- equivalence of polynomials
                  
infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : Rel Polynomial a
p ≈ₚ q = ⟦ p ⟧ ≡ ⟦ q ⟧

_≉ₚ_ : Rel Polynomial a
p ≉ₚ q = ¬ (p ≈ₚ q)

≈ₚ-isEquivalence : IsEquivalence _≈ₚ_
≈ₚ-isEquivalence =
  record { refl = refl ; sym = λ {x y} → symₚ {x} {y} ; trans = λ {x y z} → transₚ {x} {y} {z} }
  where
    symₚ : Symmetric _≈ₚ_
    symₚ {x} {y} Hxy with ⟦ x ⟧ | ⟦ y ⟧
    ... | _ | _ = sym Hxy

    transₚ : Transitive _≈ₚ_
    transₚ {x} {y} {z} Hxy Hyz with ⟦ x ⟧ | ⟦ y ⟧ | ⟦ z ⟧
    ... | _ | _ | _ = trans Hxy Hyz

_≉0ₚ : Polynomial → Set a
p ≉0ₚ = p ≉ₚ 0ₚ
             
Polynomial≉0ₚ : Set a
Polynomial≉0ₚ = Subset Polynomial _≉0ₚ

_+ₚ_ : Op₂ Polynomial
0ₚ +ₚ q = q
(a *𝑋^ n +ₚ p) +ₚ q = a *𝑋^ n +ₚ (p +ₚ q)

_-ₚ_ : Op₂ Polynomial
0ₚ -ₚ q = q
(a *𝑋^ n +ₚ p) -ₚ q = (- a) *𝑋^ n +ₚ (p -ₚ q)

_*𝑋^_*ₚ_ : A → ℕ → Polynomial → Polynomial
a *𝑋^ n *ₚ 0ₚ = 0ₚ
a *𝑋^ n *ₚ (b *𝑋^ m +ₚ p) = (a * b) *𝑋^ (n Nat.+ m) +ₚ (a *𝑋^ n *ₚ p)

_*ₚ_ : Op₂ Polynomial
0ₚ *ₚ q = 0ₚ
(a *𝑋^ n +ₚ p) *ₚ q = (a *𝑋^ n *ₚ q) +ₚ (p *ₚ q)

postulate
  _⁻¹ₚ : Op₁ Polynomial≉0ₚ
    
_÷ₚ_ : Polynomial → Polynomial≉0ₚ → Polynomial
p ÷ₚ q| = p *ₚ elem (q| ⁻¹ₚ)

1-_*𝑋 : A → Polynomial
1- a *𝑋 = (- a) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)

postulate
  1-a*𝑋≉0ₚ : ∀ {a} → 1- a *𝑋 ≉0ₚ
  +-identityˡ : ∀ x → x + 0# ≡ x
  ^-nonzero : ∀ (x|@(x # px) : A≉0#) n → (x ^ n) ≉0#
  *-elimʳ : ∀ x y z → x ≉0# → y * x ≡ z * x → y ≡ z
  
-- ``a𝑋 ≈ b𝑋 → a ≈ b``, for ``𝑥 ≉ 0``
a𝑋ⁿ≈b𝑋ⁿ→a≡b : ∀ {a b n} →
  𝑥 ≉0# →
  (a *𝑋^ n +ₚ 0ₚ) ≈ₚ (b *𝑋^ n +ₚ 0ₚ) →
  ---------------------------------------------
  a ≡ b
a𝑋ⁿ≈b𝑋ⁿ→a≡b {a} {b} {n} 𝑥≉0# a𝑋ⁿ≈b𝑋ⁿ
  with inspect ⟦_⟧  (a *𝑋^ n +ₚ 0ₚ) | inspect ⟦_⟧  (a *𝑋^ n +ₚ 0ₚ)
... | [ refl ] | [ refl ] rewrite
      +-identityˡ (a * (𝑥 ^ n)) |
      +-identityˡ (b * (𝑥 ^ n))
      = *-elimʳ (𝑥 ^ n) a b (^-nonzero (𝑥 # 𝑥≉0#) n) a𝑋ⁿ≈b𝑋ⁿ


--
-- Power Series
--


-- Infinite power series in powers of ``𝑋``
infix 5 ∑_
data PowerSeries : Set a where
  ∑_ : (ℕ → A) → PowerSeries

∑-term : PowerSeries → ℕ → Polynomial
∑-term (∑ a-) i = a- i *𝑋^ i +ₚ 0ₚ

_≈ₛ_ : Rel PowerSeries a
(∑ a-) ≈ₛ (∑ b-) = ∀ i → a- i ≡ b- i

≈ₛ-isEquivalence : IsEquivalence _≈ₛ_
≈ₛ-isEquivalence =
  record { refl = reflₛ ; sym = symₛ ; trans = transₛ }
  where
    reflₛ : Reflexive _≈ₛ_
    reflₛ {∑ a- } = λ i → refl

    symₛ : Symmetric _≈ₛ_
    symₛ {∑ a- } {∑ b- } Hab = λ i → sym (Hab i)

    transₛ : Transitive _≈ₛ_
    transₛ {∑ a- } {∑ b- } {∑ c- } Hab Hbc = λ i → trans (Hab i) (Hbc i)


0∑ : PowerSeries
0∑ = ∑ λ _ → 0#

-- 𝑋 * ∑ aᵢ 𝑋ⁱ = ∑ aᵢ 𝑋ⁱ⁺¹
𝑋*_ : Op₁ PowerSeries
𝑋* (∑ a-) = ∑ λ { 0 → 0# ; (suc i) → a- i }

-- 𝑋ⁿ * ∑ aᵢ 𝑋ⁱ = ∑ aᵢ 𝑋ⁱ⁺ⁿ
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
scaleₛ (a *𝑋^ n +ₚ p) (∑ b-) = (𝑋^[ n ]* (∑ λ i → a * b- i)) +ₛ (scaleₛ p (∑ b-))
  
-- Convergence of power series,
-- defined by axioms, since I don't get into a fully-flushed
-- constructive formalization of infinite series from the bottom-up.
infix 4 _⟶∞_
data _⟶∞_ : PowerSeries → Polynomial → Set a where
  -- ``∑ (a𝑋)ⁱ ⟶∞ (1 - a𝑋)⁻¹``, when ``1 - a𝑋 ≢ 0`` and ``|𝑋| < ½``
  converge-rule1 : ∀ (a : A) →
    ((- a) *𝑋^ 1 +ₚ (1# *𝑋^ 0 +ₚ 0ₚ)) ≉0ₚ →
    -- ``|𝑋| < ½``
    ---------------------------------------------------------
    ∑ (λ i → a ^ i) ⟶∞ elem ((1- a *𝑋 # 1-a*𝑋≉0ₚ {a}) ⁻¹ₚ)


limit : ∀ s {p} → .(s ⟶∞ p) → Polynomial
limit _ {p} _ = p

postulate
  limit-injective : ∀ s {p} s⟶∞p s′ {p′} s′⟶∞p′ →
    limit s {p} s⟶∞p ≈ₚ limit s′ {p′} s′⟶∞p′ →
    s ≈ₛ s′


postulate
  ∑-injective : ∀ a- b- →
    (∑ a-) ≈ₛ (∑ b-) →
    ∀ i → a- i ≡ b- i
