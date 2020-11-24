module Algebra.Field.Rational where


open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Nat.Coprimality using (Coprime)
open import Data.Integer as Int using (ℤ)
open ℤ using (pos; negsuc)
open import Data.Rational as Rat using (0ℚ; 1ℚ; _+_; _*_; -_; mkℚ)
open import Data.Subset
open import Algebra.Core
open import Algebra.Field
open FieldModule


-- ----------------------------------------------------------------
-- Rationals
-- ----------------------------------------------------------------
-- The rational numbers are encoded as a pair of
-- an integer (numerator) and natural (denomenator), where
-- the denomenator is always interpreted as the successor of the
-- held natural.
-- The rationals form a field.


-- (a / b)⁻¹ = (b / a)
_⁻¹ : Op₁ (A≉0# _≡_ 0ℚ)
r@(mkℚ (pos n) b-1 isCoprime # r≢0) ⁻¹ =
  (mkℚ (pos (suc b-1)) n coprime-b-sn) # r⁻¹≢0 where
  postulate
    coprime-b-sn : Coprime (suc b-1) (suc n)
    r⁻¹≢0 : mkℚ (pos (suc b-1)) n coprime-b-sn ≢ 0ℚ
r@(mkℚ (negsuc n) b-1 isCoprime # p) ⁻¹ =
  (mkℚ (negsuc (suc b-1)) (suc n) coprime-sb-ssn) # r⁻¹≢0 where
  postulate
    coprime-sb-ssn : Coprime (suc (suc b-1)) (suc (suc n))
    r⁻¹≢0 : (mkℚ (negsuc (suc b-1)) (suc n) coprime-sb-ssn) ≢ 0ℚ

postulate
    isField-ℚ : IsField _≡_ 0ℚ 1ℚ _+_ _*_ -_ _⁻¹
    

field-ℚ : Field _ _
field-ℚ = record { isField = isField-ℚ }
