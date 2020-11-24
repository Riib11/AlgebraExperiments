-- sqrt[5]⁻¹ *ₛ (() - ())
  




  -- -- (1 - 𝑋 - 𝑋^2) f ≡ F₀ + F₁ + ∑[ Fᵢ₊₁ - Fᵢ - Fᵢ₋₁ ]
  -- postulate
  --   lem1 : t *ₚ f-limit ≡ s-limit

  -- -- f ≡ 1 / (1 - 𝑋 - 𝑋^2)
  -- postulate
  --   lem2 : t *ₚ f-limit ≡ t⁻¹

  -- φ⁺ : A
  -- φ⁺ = φ

  -- φ⁻ : A
  -- φ⁻ = 1# - φ

  -- postulate
  --   [1-φ⁺x]⁻¹ : Polynomial
  --   -- [1-φ⁺x]⁻¹ = elem (((1ₚ -ₚ (φ⁻ *𝑋^ 1)) # ?) ⁻¹ₚ)

  -- φ⁺/[1-φ⁺x] : Polynomial
  -- φ⁺/[1-φ⁺x] = ⟦ φ⁺ ↑⟧ *ₚ [1-φ⁺x]⁻¹
  
  -- postulate
  --   [1-φ⁻x]⁻¹ : Polynomial
  --   -- [1-φ⁻x]⁻¹ = elem (((1ₚ -ₚ (φ⁻ *𝑋^ 1)) # ?) ⁻¹ₚ)

  -- φ⁻/[1-φ⁻x] : Polynomial
  -- φ⁻/[1-φ⁻x] = ⟦ φ⁺ ↑⟧ *ₚ [1-φ⁻x]⁻¹

  -- -- 1 / (1 - 𝑋 - 𝑋^2) ≡
  -- -- (1/sqrt[5]) ((φ⁺ / (1 - φ⁺x)) - ((φ⁻ / (1 - φ⁻x))))
  -- postulate
  --   lem3 : t⁻¹ ≡ ⟦ sqrt[5]⁻¹ ↑⟧ *ₚ (φ⁺/[1-φ⁺x] -ₚ φ⁻/[1-φ⁻x])

  -- postulate
  --   [1-_𝑋]⁻¹ : A → Polynomial
  --   -- [1- a 𝑋]⁻¹ = elem (((1ₚ -ₚ (a *𝑋^ 1)) # {!!}) ⁻¹ₚ)

  -- postulate
  --   lem4 : ∀ a n {p} → ∑ (λ i → (a ^ n) *𝑋^ n) ∞⟶ p →
  --     [1- a 𝑋]⁻¹ ≡ p
  
  -- postulate
  --   p⁺ : Polynomial

  -- postulate
  --   p⁻ : Polynomial

  -- postulate
  --   lem5 : ⟦ sqrt[5]⁻¹ ↑⟧ *ₚ ((⟦ φ⁺ ↑⟧ *ₚ [1- φ⁺ 𝑋]⁻¹) -ₚ (⟦ φ⁻ ↑⟧ *ₚ [1- φ⁻ 𝑋]⁻¹))
  --      ≡ ⟦ sqrt[5]⁻¹ ↑⟧ *ₚ ((⟦ φ⁺ ↑⟧ *ₚ p⁺) -ₚ (⟦ φ⁻ ↑⟧ *ₚ p⁻))

  -- postulate
  --   p⁺⁻ : Polynomial

  -- postulate
  --   lem6 : ⟦ sqrt[5]⁻¹ ↑⟧ *ₚ ((⟦ φ⁺ ↑⟧ *ₚ p⁺) -ₚ (⟦ φ⁻ ↑⟧ *ₚ p⁻))
  --        ≡ ⟦ sqrt[5]⁻¹ ↑⟧ *ₚ p⁺⁻

  -- equiv-sum-poly-terms : (a₁ a₂ : ℕ → A) (p₁ p₂ : Polynomial) →
  --   ∑ (λ i → a₁ i *𝑋^ i) ∞⟶ p₁ →
  --   ∑ (λ i → a₂ i *𝑋^ i) ∞⟶ p₂ → (i : ℕ) → a₁ i ≡ a₂ i

  -- postulate
  --   lem7 : ∀ n → F n ≡ sqrt[5]⁻¹ * ((φ⁺ ^ suc n) - (φ⁻ ^ suc n))
  -- -- lem7 = equiv-sum-poly-terms (λ i → F i) (λ i → sqrt[5]⁻¹ * ((φ⁺ ^ suc i) - (φ⁻ ^ suc i))) (limit (∑ (λ i → ⟦ sqrt[5]⁻¹ * ((φ⁺ ^ suc i) - (φ⁻ ^ suc i)) ↑⟧)) {!!}) {!!} {!!} {!!}

  -- lem8 : ∀ n → fibonacci n ≡ internal (sqrt[5]⁻¹ * ((φ⁺ ^ suc n) - (φ⁻ ^ suc n))
  -- lem8 = ?

  -- fibonacci-correct : ∀ n → fibonacci n ≡ fibonacci-rec n
  -- fibonacci-correct 0 = {!!}
  -- fibonacci-correct (suc n) = cong (Int.∣_∣ ∘ ℚ.numerator ∘ internal) {!!}
  --   where
  --     open IsField isField-ExtensionBySqrt
  --     sqrt[5]N = sqrt[5] # (λ ())

-- fibonacci = Int.∣_∣ ∘ ℚ.numerator ∘ internal ∘ fibonacci-extended
-- fibonacci-extended n = ((φ ^ n) - ((1# - φ) ^ n)) * elem (sqrt[5]N ⁻¹)


-- -- closed formula and recursive formula always yield same answer
-- postulate
--   fibonacci-correct : ∀ n → fibonacci n ≡ fibonacci-rec n
                                                          
