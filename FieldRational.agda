module FieldRational where


open import Relation.Binary.PropositionalEquality
open import Data.Rational
open import Algebra.Core
open import StructureField


-- ----------------------------------------------------------------
-- Rationals
-- ----------------------------------------------------------------
-- The rational numbers are encoded as a pair of
-- an integer (numerator) and natural (denomenator), where
-- the denomenator is always interpreted as the successor of the
-- held natural.
-- The rationals form a field.


postulate
    _⁻¹ : Op₁ (N _≡_ 0ℚ)
    isField-ℚ : IsField _≡_ 0ℚ 1ℚ _+_ _*_ -_ _⁻¹
    
