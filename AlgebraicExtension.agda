open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Data.Product

module Field
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Level using (_⊔_)

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures {a} {ℓ} {A} _≈_ as Structures

record IsField (+ * : Op₂ A) (- ⁻¹ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isCommutativeRing : IsCommutativeRing + * - 0# 1#
    isAbelianGroup : IsAbelianGroup * 1# ⁻¹


record IsAlgebraicFieldExtensionSqrt
  (+ * : Op₂ A) (- ⁻¹ : Op₁ A) (0# 1# : A)
  (_*ₑ_ : Op₂ (A × A)) (_≈₂_ : Rel (A × A) ℓ) (α : A)
  : Set (a ⊔ ℓ) where
  field
    isField : IsField + * - ⁻¹ 0# 1#
    ≈₂-isEquivalence : IsEquivalence _≈₂_
    extension-equation : ((0# , 1#) *ₑ (0# , 1#)) ≈₂ (α , 0#)
