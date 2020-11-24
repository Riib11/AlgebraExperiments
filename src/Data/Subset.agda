module Data.Subset where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (REL; Rel)
open import Relation.Nullary using (¬_)

open import Algebra.Core


-- ================================================================
-- Subset
-- ================================================================
-- _Subset_ types (i.e. the type of ``A``-terms that satisfy
-- predicate ``P``) are encoded by their element and a
-- proof (certificate) that the element satisfies the subset predicate.


record Subset {a b} (A : Set a) (P : A → Set b) : Set (a ⊔ b) where
  constructor _#_
  field
    elem : A
    .certificate : P elem -- proof that ``elem`` satisfies ``P``

open Subset public


-- lift a homogenous relation
Rel⌈_⌉ : ∀ {a b ℓ} {A : Set a} {P : A → Set b}
  (~ : Rel A ℓ) → Rel (Subset A P) ℓ
Rel⌈ ~ ⌉ = λ (x # _) (y # _) → ~ x y

-- Op₂⌈_⌉ : ∀ {a b} {A : Set a} {P : A → Set b}
--   (∙ : Op₂ A) → Op₂ (Subset A P)
-- Op₂⌈ ∙ ⌉ = λ (x # _) (y # _) → {!!} 

IsClosed₁ : ∀ {a b} {A : Set a} → (A → Set b) → Op₁ A → Set (a ⊔ b)
IsClosed₁ {A = A} P ⊝_ = ∀ (x : Subset A P) → P (⊝ elem x)
                                                    
IsClosed₂ : ∀ {a b} {A : Set a} → (A → Set b) → Op₂ A → Set (a ⊔ b)
IsClosed₂ {A = A} P _∙_ = ∀ (x y : Subset A P) → P (elem x ∙ elem y)
