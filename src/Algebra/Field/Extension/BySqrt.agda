open import Level
open import Relation.Binary

module Algebra.Field.Extension.BySqrt {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (α : A) where


open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Unit
open import Data.Empty

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
-- the original field.


-- extend field on ``A`` with ``sqrt[α]``
record E : Set a where
  constructor _+sqrt[α]_
  field
    internal : A
    external : A

open E public

module IsField-E
  (0# 1# : A)
  (_+_ _*_ : Op₂ A)
  (-_ : Op₁ A) (_⁻¹ : Op₁ (FieldModule.A≉0# _≈_ 0#))
  (α-squarefree : ¬ ∃[ x ] ((x * x) ≈ α)) -- required for simple `_⁻¹`
  (isField : IsField _≈_ 0# 1# _+_ _*_ -_ _⁻¹)
  where
  -- open IsField isField
  field- : Field _ _
  field- = record { isField = isField }
  open Field field-
    hiding ( _≈_ ; 0# ; 1# ; _+_ ; _*_ ; -_ ; _⁻¹ )
               
  -- extended versions of ``IsField`` fields

  infix 4 _≈′_
  _≈′_ : Rel E ℓ
  (a +sqrt[α] b) ≈′ (c +sqrt[α] d) = (a ≈ c) × (b ≈ d)

  _≉′_ : Rel E ℓ
  x ≉′ y = ¬ (x ≈′ y)

  0#′ : E
  0#′ = 0# +sqrt[α] 0#

  _≉′0#′ : Pred E ℓ
  _≉′0#′ = (_≉′ 0#′)

  1#′ : E
  1#′ = 1# +sqrt[α] 0#

  -1#′ : E
  -1#′ = -1# +sqrt[α] 0#

  sqrt[α] : E
  sqrt[α] = 0# +sqrt[α] 1#
                    
  _+′_ : Op₂ E
  (a +sqrt[α] b) +′ (c +sqrt[α] d) = (a + c) +sqrt[α] (b + d) 
                                                           
  -- extended multiplication that accounts for combined ``sqrt[α]`` terms
  _*′_ : Op₂ E
  (a +sqrt[α] b) *′ (c +sqrt[α] d) = ((a * c) + (α * (b * d))) +sqrt[α] ((a * d) + (b * c))
                                                                                        
  -′_  : Op₁ E
  -′ x = -1#′ *′ x

  _-′_ : Op₂ E
  x -′ y = x +′ (-′ y)

    
  postulate
    isCommutativeRing′ : IsCommutativeRing _≈′_ _+′_ _*′_ -′_ 0#′ 1#′

  E≉0#′ : Set (a ⊔ ℓ)
  E≉0#′ = Subset {a} {ℓ} E (_≉′ 0#′)

  _≈′|_ : Rel E≉0#′ ℓ
  _≈′|_ = Rel⌈ _≈′_ ⌉

  _≉0#′ : E → Set ℓ
  _≉0#′ = _≉′ 0#′

  _²′ : Op₁ E
  a ²′ = a *′ a

  postulate
    equiv-sqrt : ∀ {a b} → (a ²) ≈ (b ²) → a ≈ b
    equiv-sqrt-α : ∀ {a} → (a *′ a) ≈′ (α +sqrt[α] 0#) → a ≈′ (0# +sqrt[α] 1#)

  isEquivalence-≈′ : IsEquivalence _≈′_
  isEquivalence-≈′ = IsCommutativeRing.isEquivalence isCommutativeRing′ where
    open IsCommutativeRing isCommutativeRing

  module A-Properties where
    open IsCommutativeRing isCommutativeRing public
      using
        ( *-isMagma ; zeroˡ ; zeroʳ ; *-identityˡ ; *-identityʳ ; *-assoc
        ; +-isMagma ; +-identityˡ ; +-identityʳ
        ; isRing )
      renaming ()
    open IsMagma *-isMagma public
      using (refl ; sym ; trans ; isEquivalence)
      renaming (∙-cong to *-cong)
    open IsMagma +-isMagma public
      using ()
      renaming (∙-cong to +-cong)

  module ≈-Reasoning where
    open import Relation.Binary.Reasoning.Base.Single _≈_
      (IsEquivalence.refl A-Properties.isEquivalence)
      (IsEquivalence.trans A-Properties.isEquivalence)
      public
  

  module E-Properties where
    open IsCommutativeRing isCommutativeRing′ public
    
  module ≈′-Reasoning where
    open import Relation.Binary.Reasoning.Base.Single _≈′_
      (IsEquivalence.refl E-Properties.isEquivalence)
      (IsEquivalence.trans E-Properties.isEquivalence)
      public

  
  sqrt[α]²≈α : (sqrt[α] ²′) ≈′ (α +sqrt[α] 0#)
  sqrt[α]²≈α =
    begin
      (sqrt[α] ²′)
    ∼⟨ E-Properties.refl ⟩
      (sqrt[α] *′ sqrt[α])
    ∼⟨ E-Properties.refl ⟩
      ( ((0# * 0#) + (α * (1# * 1#))) +sqrt[α] ((0# * 1#) + (1# * 0#)) )
    ∼⟨ A-Properties.+-cong (A-Properties.zeroˡ 0#) A-Properties.refl , A-Properties.refl ⟩
      ( (0# + (α * (1# * 1#))) +sqrt[α] ((0# * 1#) + (1# * 0#)) )
    ∼⟨ (A-Properties.+-cong A-Properties.refl (A-Properties.*-cong A-Properties.refl (A-Properties.*-identityˡ 1#))) , A-Properties.refl ⟩
      ( (0# + (α * 1#)) +sqrt[α] ((0# * 1#) + (1# * 0#)) )
    ∼⟨ A-Properties.+-identityˡ (α * 1#) , A-Properties.refl ⟩
      ( (α * 1#) +sqrt[α] ((0# * 1#) + (1# * 0#)) )
    ∼⟨ A-Properties.*-identityʳ α , A-Properties.refl ⟩
      ( α +sqrt[α] ((0# * 1#) + (1# * 0#)) )
    ∼⟨ A-Properties.refl , (A-Properties.+-cong (A-Properties.zeroˡ 1#) A-Properties.refl) ⟩
      ( α +sqrt[α] (0# + (1# * 0#)) )
    ∼⟨ A-Properties.refl , (A-Properties.+-cong A-Properties.refl (A-Properties.zeroʳ 1#)) ⟩
      ( α +sqrt[α] (0# + 0#) )
    ∼⟨ A-Properties.refl , (A-Properties.+-identityˡ 0#) ⟩
      (α +sqrt[α] 0#)
    ∎
    where
      open import Relation.Binary.Reasoning.Base.Single _≈′_
        (IsEquivalence.refl E-Properties.isEquivalence)
        (IsEquivalence.trans E-Properties.isEquivalence)

  ¬x²≈αy|² : ∀ {x} {y| : A≉0#} → ¬ ((x * x) ≈ (α * (elem y| * elem y|)))
  ¬x²≈αy|² {x} y|@{y # py} H = ⊥-elim (α-squarefree ((x ÷ (y # py)) , ⋯≈α)) where
    open ≈-Reasoning
    ⋯≈α : ((x ÷ (y # _)) * (x ÷ (y # _))) ≈ α
    ⋯≈α =
      begin                         ((x ÷ (y # _))  * (x ÷ (y # _)))
      ∼⟨ A-Properties.sym x*y÷z*w≈x÷z*y÷w ⟩    ((x * x)        ÷ ((y * y) # _))
      ∼⟨ A-Properties.*-cong H A-Properties.refl ⟩        ((α *  (y * y)) ÷ ((y * y) # _))
      ∼⟨ A-Properties.*-assoc _ _ _ ⟩          ( α * ((y * y)  ÷ ((y * y) # x|²≉0# {y|})))
      ∼⟨ A-Properties.*-cong A-Properties.refl x*x⁻¹≈1# ⟩ (α * 1#)
      ∼⟨ A-Properties.*-identityʳ α ⟩          α
      ∎

  ¬x|²≈αy|² : ∀ {(x # _) (y # _) : A≉0#} → ¬ ((x ²) ≈ (α * (y ²)))
  ¬x|²≈αy|² x|@{x # px} y|@{y # py} H = ⊥-elim (α-squarefree ((x ÷ (y # py)) , ⋯≈α)) where
    open ≈-Reasoning
    ⋯≈α : ((x ÷ (y # _)) * (x ÷ (y # _))) ≈ α
    ⋯≈α =
      begin                         ((x ÷ (y # _))  * (x ÷ (y # _)))
      ∼⟨ A-Properties.sym x*y÷z*w≈x÷z*y÷w ⟩    ((x * x)        ÷ ((y * y) # _))
      ∼⟨ A-Properties.*-cong H A-Properties.refl ⟩        ((α *  (y * y)) ÷ ((y * y) # _))
      ∼⟨ A-Properties.*-assoc _ _ _ ⟩          ( α * ((y * y)  ÷ ((y * y) # x|²≉0# {y|})))
      ∼⟨ A-Properties.*-cong A-Properties.refl x*x⁻¹≈1# ⟩ (α * 1#)
      ∼⟨ A-Properties.*-identityʳ α ⟩          α
      ∎

  _⁻¹′  : Op₁ E≉0#′
  (a@(x +sqrt[α] y) # pa) ⁻¹′ = a⁻¹ # a⁻¹≉0#′ where
  
    d : A
    d  = (x ²) - (α * (y ²))
    postulate
      d≉0# : d ≉0#
    d| : A≉0#
    d| = d # d≉0#

    a⁻¹ : E
    a⁻¹ = (x ÷ d|) +sqrt[α] ((- y) ÷ d|)

    postulate
      a⁻¹≉0#′ : a⁻¹ ≉0#′


  postulate
    1#′≉0#′ : 1#′ ≉′ 0#′
    *′-isNonzeroClosed : IsClosed₂ _≉0#′ _*′_

  1#′| : E≉0#′
  1#′| = 1#′ # 1#′≉0#′

  _*′|_ : Op₂ E≉0#′
  ((x +sqrt[α] y) # px) *′| ((z +sqrt[α] w) # py) = ((x +sqrt[α] y) *′ (z +sqrt[α] w)) # pxyzw
    where
      postulate
        pxyzw : ((x +sqrt[α] y) *′ (z +sqrt[α] w)) ≉′ 0#′


  _÷′_ : E → E≉0#′ → E
  a ÷′ b| = a *′ elem (b| ⁻¹′)


  postulate
    *′-isAbelianGroup : IsAbelianGroup _≈′|_ _*′|_ 1#′| _⁻¹′

  isField-E : IsField _≈′_ 0#′ 1#′ _+′_ _*′_ -′_ _⁻¹′
  isField-E =
    record
      { 1#≉0# = 1#′≉0#′
      ; isCommutativeRing = isCommutativeRing′
      ; *-isNonzeroClosed = *′-isNonzeroClosed
      ; *-isAbelianGroup = *′-isAbelianGroup
      }

  
  field-E : Field a ℓ
  field-E =
    record
      { Carrier = E
      ; _≈_ = _≈′_
      ; 0# = 0#′
      ; 1# = 1#′
      ; _+_ = _+′_
      ; _*_ = _*′_
      ; -_ = -′_
      ; _⁻¹ = _⁻¹′
      ; isField = isField-E
      }
