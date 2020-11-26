module Algebra.Field.Rational where


open import Relation.Binary.PropositionalEquality -- using (_≡_; _≢_; refl; inspect; [_])
open import Relation.Nullary
open import Data.Nat as Nat using (ℕ; zero) renaming (suc to _+1)
open import Data.Nat.Coprimality using (Coprime)
open import Data.Integer as Int using (ℤ)
open ℤ renaming (pos to +_ ; negsuc to -[_+1])
open import Data.Rational as Rat using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; mkℚ)
open import Data.Subset
open import Data.Empty
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
(r@(mkℚ (+ n) d-1 coprime) # r≢0) ⁻¹ = Rat.1/_ r {n≢0} # r⁻¹≢0 where
  open import Data.Rational.Unnormalised as RatUnn
  postulate
    n≢0 : n RatUnn.≢0
    r⁻¹≢0 : ¬ Rat.1/ mkℚ (+ n) d-1 coprime ≡ 0ℚ
(r@(mkℚ (-[ n +1]) d-1 coprime) # r≢0) ⁻¹ = Rat.1/_ r {n+1≢0} # r⁻¹≢0 where
  open import Data.Rational.Unnormalised as RatUnn
  postulate
    coprime′ : Coprime (d-1 +1) (n +1)
    n+1≢0 : (n +1) RatUnn.≢0
    r⁻¹≢0 : ¬ mkℚ -[ d-1 +1] n coprime′ ≡ 0ℚ


postulate
  isField-ℚ : IsField _≡_ 0ℚ 1ℚ _+_ _*_ -_ _⁻¹
    

field-ℚ : Field _ _
field-ℚ = record { isField = isField-ℚ }
