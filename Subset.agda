module Subset {a b} where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)

open import Algebra.Core


-- ================================================================
-- Subset
-- ================================================================
-- _Subset_ types (i.e. the type of ``A``-terms that satisfy
-- predicate ``P``) are encoded by their element and a
-- proof (certificate) that the element satisfies the subset predicate.


record Subset (A : Set a) (P : A → Set b) : Set (a ⊔ b) where
  constructor _#_
  field
    elem : A
    .certificate : P elem -- proof that ``elem`` satisfies ``P``

open Subset public


IsClosed₁ : {A : Set a} → (A → Set b) → Op₁ A → Set (a ⊔ b)
IsClosed₁ {A = A} P ⊝_ = ∀ (x : Subset A P) → P (⊝ elem x)
                                                    
IsClosed₂ : {A : Set a} → (A → Set b) → Op₂ A → Set (a ⊔ b)
IsClosed₂ {A = A} P _∙_ = ∀ (x y : Subset A P) → P (elem x ∙ elem y)
