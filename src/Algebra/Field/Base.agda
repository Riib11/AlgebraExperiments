module Algebra.Field.Base where


open import Level using (_⊔_; suc)
open import Relation.Binary -- using (Rel)
open import Relation.Unary
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable

open import Algebra.Core
open import Algebra.Structures as Structures
open import Algebra.Bundles as Bundles

open import Data.Subset
open import Data.Product


-- ================================================================
-- Field
-- ================================================================
-- A _field_ is an setoid algebraic structure
-- with two binary operations, ``+`` and ``*``,
-- that satisfy the following properties:
-- 1. ``+`` is associative
-- 2. ``+``, ``*`` are commutative
-- 3. ``+``, ``*`` have identities ``0#``, ``1#`` respectively (i.e. monoids)
-- 4. ``+`` has inverse ``-`` (i.e. group)
-- 5. ``*`` has inverse ``⁻¹`` on nonzero elements (i.e. group over nonzeros)
-- 6. ``*`` distributes over ``+`` (i.e. ring)

module FieldModule {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (0# : A) where
  open import Algebra.Structures as Structures

  -- not ``x ≈ y``
  _≉_ : Rel A ℓ
  x ≉ y = ¬ (x ≈ y)

  -- ``x`` is not ``≈`` to ``0#``
  _≉0# : Pred A ℓ
  _≉0# = _≉ 0#

  -- The type of ``A``-terms that are not setoid-equivalent to 0#
  A≉0# : Set (a ⊔ ℓ)
  A≉0# = Subset {a} {ℓ} A _≉0#
  
  -- ``_≈_`` restricted to nonzeros
  ≈| : Rel A≉0# ℓ
  ≈| (x # _) (y # _) = x ≈ y

  module _ (1# : A) (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (_⁻¹ : Op₁ A≉0#) where

    -- ``_*_`` restricted to nonzeros
    *| : (IsClosed₂ _≉0# _*_) → Op₂ A≉0#
    *| H nx@(x # px) ny@(y # py) = (x * y) # (H nx ny)

    ÷ : A → A≉0# → A
    ÷ a b| = a * elem (b| ⁻¹)

    -- ``1#`` included as a nonzero
    1#| : (1# ≉ 0#) → A≉0#
    1#| 1#≉0# = 1# # 1#≉0#

    2# : A
    2# = 1# + 1#
    
    postulate
      2#| : A≉0#
                          
    record IsField : Set (a ⊔ ℓ) where
      field
        1#≉0# : 1# ≉ 0#
        isCommutativeRing     : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
        *-isNonzeroClosed     : IsClosed₂ _≉0# _*_
        *-isAbelianGroup      : IsAbelianGroup ≈| (*| *-isNonzeroClosed) (1#| 1#≉0#) _⁻¹
    


module _ where
  open FieldModule public
    renaming
      ( _≉0# to _raw-≉0#
      ; A≉0# to raw-A≉0#
      ; ≈| to raw-≈|
      ; *| to raw-*|
      ; ÷ to raw-÷
      ; 1#| to raw-1#|
      ; 2# to raw-2# ; 2#| to raw-2#| )


  record Field a ℓ : Set (suc (a ⊔ ℓ)) where
    infix  9 _⁻¹
    infix  8 -_
    infixl 7 _*_
    infixl 6 _+_
    infixl 6 _-_
    infix  4 _≈_
    field
      Carrier : Set a
      _≈_ : Rel Carrier ℓ
      0#  : Carrier
      1#  : Carrier
      _+_ : Op₂ Carrier
      _*_ : Op₂ Carrier
      -_  : Op₁ Carrier
      _⁻¹ : Op₁ (FieldModule.A≉0# _≈_ 0#)
      isField : FieldModule.IsField _≈_ 0# 1# _+_ _*_ -_ _⁻¹
  
    open IsField isField public

    private
      A : Set a
      A = Carrier
  
    A≉0# : Set (a ⊔ ℓ)
    A≉0# = raw-A≉0# _≈_ 0#

    _≉0# : Pred A ℓ
    _≉0# = _raw-≉0# _≈_ 0#
  
    _≈|_ : Rel A≉0# ℓ
    _≈|_ = raw-≈| _≈_ 0#
  
    _*|_ : Op₂ A≉0#
    _*|_ = raw-*| _≈_ 0# 1# _+_ _*_ -_ _⁻¹ *-isNonzeroClosed
  
    _÷_ : Carrier → A≉0# → Carrier
    _÷_ = raw-÷ _≈_ 0# 1# _+_ _*_ -_ _⁻¹ 
  
    1#| : A≉0#
    1#| = raw-1#| _≈_ 0# 1# _+_ _*_ -_ _⁻¹ 1#≉0#
    
  
    commutativeRing : CommutativeRing _ _
    commutativeRing = record { isCommutativeRing = isCommutativeRing }
  
    _-_ : Op₂ A
    x - y = x + (- y)

    _² : Op₁ A
    x ² = x * x
    
    --
    -- useful lemmas about fields
    --

    postulate
      *-preserves-≉0# : ∀ {a b} → a ≉0# → b ≉0# → (a * b) ≉0#
      a-b≈0#→a≈b : ∀ {a b} → a - b ≈ 0# → a ≈ b

    -1# : A
    -1# = - 1#

    2# : A
    2# = raw-2# _≈_ 0# 1# _+_ _*_ -_ _⁻¹
  
    2#| : A≉0#
    2#| = 2# # 2#≉0# where
      postulate
        2#≉0# : 2# ≉0#

    3# : A
    3# = 2# + 1#

    4# : A
    4# = 3# + 1#

    5# : A
    5# = 4# + 1#

    6# : A
    6# = 5# + 1#

    7# : A
    7# = 6# + 1#
                   
    open import Relation.Binary.Reasoning.Base.Single _≈_
      (IsEquivalence.refl (Ring.isEquivalence (CommutativeRing.ring commutativeRing)))
      (IsEquivalence.trans (Ring.isEquivalence (CommutativeRing.ring commutativeRing)))

    module _ where
      open CommutativeRing commutativeRing
        hiding
          ( _≈_ ; _+_ ; _-_ ; -_ ; _*_ ; 0# ; 1# )
      open IsAbelianGroup *-isAbelianGroup
        using (inverse)

      postulate
        x|*y|≉0# : ∀ {x| y| : A≉0#} → (elem x| * elem y|) ≉0#
        x|²≉0# : ∀ {x| : A≉0#} → (elem x| ²) ≉0#
        x*x⁻¹≈1# : ∀ {x| : A≉0#} → (elem x| * elem (x| ⁻¹)) ≈ 1#
        x*y÷z*w≈x÷z*y÷w : ∀ {x y} {z| w| : A≉0#} →
          ((x * y) ÷ ((elem z| * elem w|) # (x|*y|≉0# {z|} {w|}))) ≈ ((x ÷ z|) * (y ÷ w|))
        x-x≈0# : ∀ {x} → (x - x) ≈ 0#
        -1*x≈-x : ∀ {x} → (-1# * x) ≈ (- x)

      x≈y*z→x÷z≈y : ∀ {x y z|} → x ≈ (y * elem z|) → (x ÷ z|) ≈ y
      x≈y*z→x÷z≈y {x} {y} {z # pz} H =
        begin
          (x ÷ (z # pz))
        ∼⟨ *-cong H refl ⟩
          ((y * z) ÷ (z # pz))
        ∼⟨ refl ⟩
          ((y * z) * elem ((z # pz) ⁻¹))
        ∼⟨ *-assoc y z (elem ((z # pz) ⁻¹)) ⟩
          (y * (z * elem ((z # pz) ⁻¹)))
        ∼⟨ *-cong refl x*x⁻¹≈1# ⟩
          (y * 1#)
        ∼⟨ *-identityʳ y ⟩
          y
        ∎
  
    open CommutativeRing commutativeRing public
      using
        ( +-rawMagma; +-magma; +-semigroup; +-commutativeSemigroup
        ; *-rawMagma; *-magma; *-semigroup
        ; +-rawMonoid; +-monoid ; +-commutativeMonoid
        ; *-rawMonoid; *-monoid
        ; nearSemiring; semiringWithoutOne
        ; semiringWithoutAnnihilatingZero
        ; isRing; +-abelianGroup
        )
