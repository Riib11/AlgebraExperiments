open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Algebra.Field
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _^_ to _^ℕ_)
open import Data.Nat.Properties

module Algebra.Field.Exponentiation {a ℓ} (F : Field a ℓ) where

open Field F renaming (Carrier to A)

-- linear exponentiation
_^_ : A → ℕ → A
x ^ 0 = 1#
x ^ suc n = x * (x ^ n)
                     
⌊_/2⌋-remainder : (n : ℕ) → ∃[ n′ ] ((n ≡ n′ +ℕ n′) ⊎ (n ≡ suc (n′ +ℕ n′)))
⌊ 0 /2⌋-remainder = 0 , (inj₁ refl)
⌊ suc n /2⌋-remainder with ⌊ n /2⌋-remainder
... | n′ , inj₁ n≡2n′ rewrite n≡2n′ = n′ , inj₂ refl
... | n′ , inj₂ n≡s2n′ rewrite n≡s2n′ | sym (+-suc n′ n′) = suc n′ , inj₁ refl

-- for fun, this is exponentiation via repeated squaring;
-- using binary representations, this can slightly speed up exponentiation
-- x ^₂ (2 * n) = (x ^₂ n) * (x ^₂ n)
{-# TERMINATING #-} -- since n′ < n
_^₂_ : A → ℕ → A
x ^₂ 0 = 1#
x ^₂ n@(suc _) with ⌊ n /2⌋-remainder
... | n′ , inj₁ n≡2n′   = (x ^₂ n′) * (x ^₂ n′) 
... | n′ , inj₂ n≡2n′+1 = ((x ^₂ n′) * (x ^₂ n′)) * x

postulate
  ^₂-correct : ∀ x n → x ^ n ≡ x ^₂ n

-- -- example: correct for ``2 ^ 10``
-- _ : 2# ^ 10 ≡ 2# ^₂ 10
-- _ = refl
