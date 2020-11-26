# README

- [Module Organization](#Module-Organization)
- [Fibonacci Sequence via Recursive Definition](#Fibonacci-Sequence-via-Recursive-Definition)
- [Fibonacci via Closed Formula](#Fibonacci-via-Closed-Formula)
- [Fields](#Fields)
- [Algebraic Field Extensions by Square Root of Square-Free Number](#Algebraic-Field-Extensions-by-Square-Root-of-Square-Free-Number)
- [Tasks](#Tasks)

## Module Organization

```
Fibonacci/           # the nth Fibonacci number
Recursive.agda       # - recursive definition
Closed.agda          # - closed definition and correctness

Algebra/             # algebraic structures

Field/               # - fields
Base.agda            #   - formalization of mathematical field
Rational.agda        #   - instantiation of the rational field
Exponentiation.agda  #   - natural exponentation over fields
Polynomial.agda      #   - polynomials over fields
Field.agda

Extension/           # - field extensions (FE)
Algebraic/           #   - algebraic field extensions (AFE)
	  E.agda         #   - AFE by square root
  E5.agda            #   - AFE of ℚ by sqrt[5]

Data/                # general data structures
Subset.agda          # - predicated terms
```


## Fibonacci Sequence via Recursive Definition

The Fibonacci sequence is a well-known sequence of natural numbers, and it is typically defined recursively as follows:

```
The 0th Fibonacci number is 0.
The 1st Fibonacci number is 1.
The (n+2)th Fibonacci number is the sum of the (n+1)th and nth Fibonacci numbers, for n ≥ 0.
```

The module `Fibonacci.Recursive` implements a function `fibonacci-recursive : ℕ → ℕ` that meets the specification above exactly. It is constructed as follows:

```agda
fibonacci-recursive : ℕ → ℕ
fibonacci-recursive 0       = 0
fibonacci-recursive 1       = 1
fibonacci-recursive (suc (suc n)) = ficonacci-rec (suc n) + fibonacci-recursive n
```

## Fibonacci via Closed Formula

There is in fact a closed formula for the nth Fibonacci number, which is the following:

```
The nth Fibonacci number is (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

where `φ = (1/2)(1 + sqrt[5])` is the golden ratio.
See `doc/fibonacci/main.pdf` for a mathematical deriviation of this closed form.
Just as before, we can formalize this specification in Agda straightforwardly:

```agda
fibonacci-extended n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

Observe that the type signature is missing --- let us derive what it must be.
For `fibonacci-recursive`, we only needed addition, and so were safely working over just monoid of addition over `ℕ`, and so the signature `ℕ → ℕ` was perfectly safe.
However, in `fibonacci-extended`, there are few new capabilities used.
1. To use subtraction, we must have an addition group.
2. To use exponentiation, we must have a multiplication monoid.
3. To use division by nonzero elements, we must have a multiplication group over nonzero elements.

(1.) and (2.) require that we have a (commutative) ring.
Then (3.) requires further that we have a field.
Since our result must eventually be reducible to a natural number,
the field to use should be the rational number field, `ℚ`.
Additionally since we are using `sqrt[5]` we must also extend `ℚ` with `sqrt[5]`, written `ℚ[sqrt[5]]`.
Since `sqrt[5]` is a zero of the `ℚ`-polynomial `X^2 - 5` (i.e. is algebraic), this is an algebraic field extension, which is a field itself.

So, we can type `fibonacci-extended` like so:

```agda
fibonacci-extended : ℕ → ℚ[sqrt[5]]
fibonacci-extended n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

But how exactly is `ℚ[sqrt[5]]` defined in Agda?
First we formalize fields in Agda
(the Agda standard library only defines algebraic structures up to commutative rings and distributive lattices).
Then we formalize algebraic field extensions by a the square root of a square-free number.

## Fields

The following is an oversimplified formalization of a Field.
The fully-detailed construction is given in the module `Algebra.Field.Base`.

```agda
record IsField
       {a ℓ : Level} {A : Set a}
       (_≈_ : Rel A ℓ)
       (0# : A) (1# : A)
       (_+_ _*_ : Op₂ A) (-_ : Op₁ A)
       (_⁻¹ : Op₁ A≉0#)
       : Set (a ⊔ ℓ)
  where
    field
      1#≉0# : 1# ≉ 0#
      isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
      *-isNonzeroClosed : IsClosed₂ _≉0# _*_
      *-isAbelianGroup  : IsAbelianGroup _≈|_ _*|_ 1#| _⁻¹
```

Parameters:
- `A` is the carrier (i.e. underlying type) of the field
- `_≈_` is the equivalence relation on `A`
- `0#` is the additive identity
- `1#` is the multiplicative identity
- `_+_`, `_*_`, `-_` are the addition, multiplication, and additive inverse operations (to form a commutative ring)
- `_⁻¹` is the multiplicative inverse on nonzero terms

Properties:
- `1#≉0#`: there is at least one nonzero term; implemented using `Data.Subset`
- `isCommutativeRing`: `_+_`, `_*_`, `-_` form a commutative ring
- `*-isNonzeroClosed`: the product of nonzero terms is nonzero
- `*-isAbelianGroup`: `_*|_`, `_⁻¹` form an abelian group with identity `1#|`, where `_*|_` is `_*_` restricted to nonzero terms and `1#|` is `1#` included as a nonzero term

Together, these properties yield a mathematical field that satisfies the following field axioms:
1. `_+_` is associative
2. `_+_`, `_*_` are commutative
3. `_+_`, `_*_` have identities `0#`, `1#` respectively (i.e. monoids)
4. `_+_` has inverse `-` (i.e. group)
5. `_*_` has inverse `⁻¹` on nonzero elements (i.e. group over nonzeros)
6. `_*_` distributes over `_+_` (i.e. ring)

## Algebraic Field Extensions by Square Root of Square-Free Number

A field can be extended by adding new terms and extending the field operations such that the result is still a field.
Further, a field extension is called __algebraic__ if the extension is by a term that is the zero of a polynomial with coefficients in original field.
For example, the complex number field are an algebraic field extension of the real number field by the zero of the polnomial `X^2 + 1`.
A nonexample is the real number field as an extension of the rational numbers, since there are real numbers such as `π` that are not the zero of any polynomial over the rationals (i.e. `π` is transcendental).

A simple procedure for producing some algebraic field extensions is by extending by the zero of the polynomial `X^2 + α`, where `α` is square-free in the original field.
We can encode a term in such a field extension as follows, which is defined in `Algebra.Field.Extension.BySqrt`.

```agda
record E : Set a where
  constructor _+sqrt[α]_
  field
    internal : A
    external : A
```

Here, `A` is the original field.
For a term of `E`,
its `internal` component resides in the original field,  and
the `external` component is extended by the new term `sqrt[α]`.

Then we can define the extended terms necessary to form a field in terms of the origiginal field's terms.
The `′` suffix indicates that the term is the extended version of the usual field term.

```agda
0#′ : E
0#′ = 0# +sqrt[α] 0#

1#′ : E
1#′ = 1# +sqrt[α] 0#

-1#′ : E
-1#′ = -1# + sqrt[α] 0#

_≈′_ : Rel E ℓ
(a +sqrt[α] b) ≈′ (c +sqrt[α] d) = (a ≈ c) × (b ≈ d)

_+′_ : Op₂ E
(a +sqrt[α] b) +′ (c +sqrt[α] d) = (a + c) +sqrt[α] (b + d)

_*′_ : Op₂ E
(a +sqrt[α] b) *′ (c +sqrt[α] d) =
    ((a * c) + (α * (b * d))) +sqrt[α]
    ((a * d) + (b * c))

-′_  : Op₁ E
-′ x = -1#′ *′ x

-- omitted proofs of ≉0#′
_⁻¹′  : Op₁ E≉0#′
(a@(x +sqrt[α] y) # pa) ⁻¹′ =
    ((  x  ÷ ((x ²) - (α * (y ²)) # _)) +sqrt[α]
    ((- y) ÷ ((x ²) - (α * (y ²)) # _))) # _
```

From all this we can construct the `IsField` instance for a field extension.

```agda
isField-ExtensionE : IsField _≈′_ 0#′ 1#′ _+′_ _*′_ -′_ _⁻¹′
isField-ExtensionE = _ -- omitted proofs of field properties
```


## Tasks

- algebraic structures
  - [x] formalization of fields; in `Algebra.Field.Base` as `IsField`
    - [x] implement natural exponentiation over fields
      - [ ] implement fast natural exponentiation over fields using repeated squaring and binary representations
  - [x] formalization of algebraic field extension by square-free square root; in `Algebra.Field.Base.Extension.BySqrt`
    - [ ] prove that such an extension is a field i.e. fill in details for `isField-E`
  - [x] `IsField` instantiation for `ℚ[sqrt[5]]`; in `Algebra.Field.Base.Extension.BySqrt5`
  - [x] formalization of polynomials over fields; in `Algebra.Field.Polynomial`
      - [ ] implement multiplicative inverse for nonzero polynomials
      - [x] implement polynomial equivalence via normalization
      - [ ] prove that polynomial equivalence is an equivalence relation
  - [x] formalization of power series over fields; in `Algebra.Field.Polynomial`
    - [ ] implement power series equivalence
    - [ ] prove that power series equivalence is an equivalence relation
    - [x] formalization of convergence of power series
      - [ ] define constructively rather than postulating convergence rules
    - [ ] prove that taking the limit of a convergent power series in injective
    - [x] prove that power series construction is injective
- Fibonacci sequence
  - [x] implementation of recursive `fibonacci`; in `Fibonacci.Recursive`
  - [x] implementation of closed `fibonacci`; in `Fibonacci.Closed`
  - [x] correctness proof of embedding recursive `fibonacci` into `ℚ[sqrt[5]]`; as `F′≡F`
  - [x] correctness proof of Fibonacci closed form
    - [x] prove `g₀ ≈ₛ g₁`
    - [ ] prove `g₁ ≈ₛ g₂`
    - [ ] prove `g₃ ⟶∞ g₄`
    - [ ] prove `f₀ ⟶∞ f₁`
    - [ ] prove `f₁ ≈ₚ f₂`
    - [ ] prove `f₃ ⟶∞ f₂`
    - [ ] prove `f₃ ≈ₛ f₄`
    - [x] prove `f₀ ≈ₛ f₃`
    - [x] prove `f₀ ≈ₛ f₄`
    - [x] prove `F (n +1) ≡ h (n +1)`
    - [x] prove `F n ≡ h n`
    - [x] prove `fibonacci-extendedended n ≡ F′ n`
    - [x] prove main theorem: `fibonacci-extendedracted n ≡ fibonacci-recursiveursive n`
