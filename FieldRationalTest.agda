module FieldRationalTest where


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


    open import Relation.Nullary
    open import Data.Unit
  open import Data.Empty
  open import Data.Bool
  import Data.Bool.Properties as BoolProperties
  open import Data.Rational as Rational
  open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
  open import Data.Integer.Base as ℤ using (ℤ; ∣_∣; +_; +0; -[1+_])
  open import Data.Nat as Nat using (zero; suc)
  open import Data.Nat.Properties as NatProperties
  open import Data.Nat.GCD as GCD
  open import Data.Nat.Divisibility as ℕDiv using (divides; 0∣⇒≡0)
  open import Data.Nat.Coprimality as C

  lem1 : ∀ (sx : N _≃_ 0ℚ) → ∣ ↥ elem sx ∣ ≢0
  lem1 (mkℚ a b-1 isCoprime # p) = {!!}

  lem2 : (x : ℚ) → ∣ ↥ x ∣ ≢0 → ¬ 1/ x ≡ 0ℚ
  lem2 (mkℚ (+_ zero) zero isCoprime) ()
  lem2 (mkℚ +[1+ n ] zero isCoprime) n≢0 ()
  lem2 (mkℚ (-[1+_] n) zero isCoprime) n≢0 ()
  lem2 (mkℚ a (Nat.suc b-1) isCoprime) n≢0 CH = {!!}

  -- test1 : ∀ n → (1/ mkℚ (+ n) zero {!!}) ≡ (mkℚ +[1+ zero ] (Nat.suc n) {!!})
  -- test1 zero rewrite refl = {!!}
  -- test1 (Nat.suc n) = {!!}

  lem4 : (x : ℚ) → 1/ x ≡ 0ℚ → x ≡ 0ℚ
  lem4 (mkℚ (+_ n) zero isCoprime) C = {!!}
  lem4 (mkℚ (+_ n) (Nat.suc b-1) isCoprime) C = {!!}

  no-bad-inverses : ∀ (x : ℚ) → .{x≢0 : ∣ ↥ x ∣ ≢0} → (1/_ x {x≢0}) ≢ 0ℚ
  no-bad-inverses x x≢0 = {!!}

  ≡0ℚ→∣↥∣≡0 : (x : ℚ) → .(x ≡ 0ℚ) → ∣ ↥ x ∣ ≡ 0
  ≡0ℚ→∣↥∣≡0 (mkℚ +0 0 _) H = refl

  lem10 : n ≢ 0 → BoolProperties.T? (n Nat.≡ᵇ 0)

  coerce≢0 : (n : Nat.ℕ) → (n ≢ 0) → n ≢0
  coerce≢0 n n≢0 rewrite refl = {!!}
  -- coerce≢0 zero H = ⊥-elim (H refl)
  -- coerce≢0 (Nat.suc n) H = {!!}
  
  ≢0ℚ→∣↥∣≢0 : (x : ℚ) → .(x ≢ 0ℚ) → ∣ ↥ x ∣ ≢0
  ≢0ℚ→∣↥∣≢0 x H = {!!}
  -- rewrite refl = {!!} where
  --   pf1 : BoolProperties.T? (∣ ↥ x ∣ Nat.≡ᵇ 0) ≡ (false because ofⁿ {!!})
  --   pf1 = {!!}
  --   pf2 : ¬ T (∣ ↥ x ∣ Nat.≡ᵇ 0)
  --   pf2 H₂ rewrite refl = {!!}
  --   pf3 : (∣ ↥ x ∣ Nat.≡ᵇ 0) ≡ false
  --   pf3 = {!!}
  -- ∣ ↥ x ∣ ≢0
  -- False (∣ ↥ x ∣ ℕ.≟ 0)
  -- T (not ∘ isYes (∣ ↥ x ∣ ℕ.≟ 0))
  --
  -- T : Bool → Set
  -- T true  = ⊤
  -- T false = ⊥
  --
  -- Coprime : Rel ℕ 0ℓ
  -- Coprime m n = ∀ {i} → i ∣ m × i ∣ n → i ≡ 1
  -- Coprime zero (suc b-1) = ∀{i} → i | zero × i | (suc b-1) → i ≡ 1

  lem5 : (sx : N _≡_ 0ℚ) → ∣ ↥ elem sx ∣ ≢0
  lem5 (mkℚ (+_ a) b-1 isCoprime # p) = {!!}
  lem5 (mkℚ (-[1+_] a) b-1 isCoprime # p) = {!!}
  
  1/N≢0 : (sx : N _≡_ 0ℚ) → (1/_ (elem sx) {lem5 sx}) ≢ 0ℚ
  1/N≢0 (x # p) CH = {!!}

  _⁻¹ : Op₁ (N _≡_ 0ℚ)
  _⁻¹ sx = (1/ elem sx) # 1/N≢0 sx

  *-isNonzeroClosed : isClosed₂ (≉0# _≡_ 0ℚ) _*_
  *-isAbelianGroup : IsAbelianGroup (_≡_ ≈| 0ℚ) (*| _≡_ 0ℚ 1ℚ _+_ _*_ -_ _⁻¹ ?) (1#| _≡_ 0ℚ 1ℚ _+_ _*_ -_ _⁻¹ ?) _⁻¹
