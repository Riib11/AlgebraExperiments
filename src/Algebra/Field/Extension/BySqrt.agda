open import Level
open import Relation.Binary

module Algebra.Field.Extension.BySqrt {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (α : A) where


open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Unit

open import Algebra.Core
open import Algebra.Structures
open import Algebra.Field

open import Data.Subset


-- ================================================================
-- Algebraic Field Extension by Square Root
-- ================================================================
-- An alegebraic field extension is a field that is formed by
-- adding external elements to a field. Specifically, we shall be
-- dealing with the method of adding a root that did not exist in
-- the original field. (If the root does did exist, then the new
-- field is trivially the same.)


-- extend field on ``A`` with ``sqrt[α]``
record BySqrt : Set a where
  constructor _+sqrt[α]_
  field
    internal : A
    external : A

open BySqrt public


module IsField-ExtensionBySqrt
  (0# 1# : A)
  (_+_ _*_ : Op₂ A)
  (-_ : Op₁ A) (_⁻¹ : Op₁ (N _≈_ 0#))
  (isField : IsField _≈_ 0# 1# _+_ _*_ -_ _⁻¹)
  where
    
  open IsField isField
               
  -- extended versions of ``IsField`` fields

  _≈′_ : Rel BySqrt ℓ
  (a +sqrt[α] b) ≈′ (c +sqrt[α] d) = (a ≈ c) × (b ≈ d)
                                                    
  0#′ : BySqrt
  0#′ = 0# +sqrt[α] 0#
                    
  1#′ : BySqrt
  1#′ = 1# +sqrt[α] 0#
                    
  _+′_ : Op₂ BySqrt
  (a +sqrt[α] b) +′ (c +sqrt[α] d) = (a + c) +sqrt[α] (b + d) 
                                                           
  -- extended multiplication that accounts for combined ``sqrt[α]`` terms
  _*′_ : Op₂ BySqrt
  (a +sqrt[α] b) *′ (c +sqrt[α] d) = ((a * c) + (α * (b * d))) +sqrt[α] ((a * d) + (b * c))
                                                                                        
  -′_  : Op₁ BySqrt
  -′ (a +sqrt[α] b) = (- a) +sqrt[α] (- b)

  _-′_ : Op₂ BySqrt
  x -′ y = x +′ (-′ y)

  postulate
    _⁻¹′  : Op₁ (N _≈′_ 0#′)

  postulate
    1#′≉0#′ : (_≈′_ ≉ 0#′) 1#′ 0#′

  postulate
    isCommutativeRing′ : IsCommutativeRing _≈′_ _+′_ _*′_ -′_ 0#′ 1#′
    IsDistributiveLattice′ : IsDistributiveLattice _≈′_ _+′_ _*′_
    *′-isNonzeroClosed : IsClosed₂ (≉0# _≈′_ 0#′) _*′_
    *′-isAbelianGroup : IsAbelianGroup (_≈′_ ≈| 0#′)
      (*| _≈′_ 0#′ 1#′ _+′_ _*′_ -′_ _⁻¹′ *′-isNonzeroClosed)
      (1#| _≈′_ 0#′ 1#′ _+′_ _*′_ -′_ _⁻¹′ 1#′≉0#′) _⁻¹′

  isField-ExtensionBySqrt : IsField _≈′_ 0#′ 1#′ _+′_ _*′_ -′_ _⁻¹′
  isField-ExtensionBySqrt =
    record
      { 1#≉0# = 1#′≉0#′
      ; isCommutativeRing = isCommutativeRing′
      ; isDistributiveLattice = IsDistributiveLattice′
      ; *-isNonzeroClosed = *′-isNonzeroClosed
      ; *-isAbelianGroup = *′-isAbelianGroup
      }

  
