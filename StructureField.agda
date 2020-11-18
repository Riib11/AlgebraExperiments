module StructureField where


open import Level using (_⊔_; suc; 0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable

open import Algebra.Core
open import Algebra.Structures as Structures

open import Subset


-- ================================================================
-- Field
-- ================================================================
-- A _field_ is an setoid algebraic structure
-- with two binary operations, ``+`` and ``*``,
-- that satisfy the following properties:
-- 1. ``+`` is associative
-- 2. ``+``, ``*`` are commutative
-- 3. ``+``, ``*`` have identities ``0#``, ``1#`` respectively (i.e. monoid)
-- 4. ``+`` has inverse ``-`` (i.e. group)
-- 5. ``*`` has inverse ``⁻¹`` on nonzero elements (i.e. group on nonzeros)
-- 6. ``*`` distributes over ``+`` (i.e. distributive lattice)

module _ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (0# : A) where
  open import Algebra.Structures as Structures

  -- not ``x ≈ y``
  _≉_ : Rel A ℓ
  x ≉ y = ¬ (x ≈ y)

  -- ``x`` is not ``≈`` to ``0#``
  ≉0# : A → Set ℓ
  ≉0# = _≉ 0#

  -- The type of ``A``-terms that are not setoid-equivalent to 0#
  N : Set (a ⊔ ℓ)
  N = Subset {a} {ℓ} A ≉0#
  
  -- ``_≈_`` restricted to nonzeros
  _≈|_ : Rel N ℓ
  (x # _) ≈| (y # _) = x ≈ y

  module _ (1# : A) (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (_⁻¹ : Op₁ N) where

    -- ``_*_`` restricted to nonzeros
    *| : (IsClosed₂ ≉0# _*_) → Op₂ N
    *| H nx@(x # px) ny@(y # py) = (x * y) # (H nx ny)

    -- ``1#`` included as a nonzero
    1#| : (1# ≉ 0#) → N
    1#| 1#≉0# = 1# # 1#≉0#

    record IsField : Set (a ⊔ ℓ) where
      field
        1#≉0# : 1# ≉ 0#
        isCommutativeRing     : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
        isDistributiveLattice : IsDistributiveLattice _≈_ _+_ _*_
        *-isNonzeroClosed     : IsClosed₂ ≉0# _*_
        *-isAbelianGroup      : IsAbelianGroup _≈|_ (*| *-isNonzeroClosed) (1#| 1#≉0#) _⁻¹


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
    _⁻¹ : Op₁ (N _≈_ 0#)
    isField : IsField _≈_ 0# 1# _+_ _*_ -_ _⁻¹

  _-_ : Op₂ Carrier
  x - y = x + (- y)

