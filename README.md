# README

## Module Organization

```
    Fibonacci/               # the nth Fibonacci number
      Recursive.agda         # - recursive definition
      Closed.agda            # - closed definition and correctness

    Algebra/                 # algebraic structures

      Field/                 # - fields
        Base.agda            #   - formalization of mathematical field
        Rational.agda        #   - instantiation of the rational field
        Exponentiation.agda  #   - natural exponentation over fields
        Polynomial.agda      #   - polynomials over fields
      Field.agda

      Extension/             # - field extensions (FE)
        Algebraic/           #   - algebraic field extensions (AFE)
		  BySqrt.agda        #     - AFE by square root
          BySqrt5.agda       #     - AFE of ℚ by sqrt[5]

    Data/                    # general data structures
      Subset.agda            # - predicated terms
```


## Fibonacci via Recursive Formula

The Fibonacci sequence is a well-known sequence of natural numbers, and it is typically defined recursively as follows:

```
    The 0th Fibonacci number is 0.
    The 1st Fibonacci number is 1.
    The (n+2)th Fibonacci number is the sum of the (n+1)th and nth Fibonacci numbers, where n ≥ 0.
```

The module `Fibonacci.Recursive` implements a function `fibonacci-rec : ℕ → ℕ` that meets the specification above exactly. It is constructed as follows:

```agda
    fibonacci-rec : ℕ → ℕ
	fibonacci-rec 0             = 0
	fibonacci-rec 1             = 1
	fibonacci-rec (suc (suc n)) = ficonacci-rec (suc n) + fibonacci-rec n
```

## Fibonacci via Closed Formula over ℚ[sqrt[5]]

There is in fact a closed formula for the nth Fibonacci number, which is the following:

```
    The nth Fibonacci number is (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

where `φ = (1/2)(1 + sqrt[5])` is the golden ratio.
Just as before, we can formalize this specification in Agda straightforwardly:

```agda
    fibonacci-ext n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

Observe that the type signature is missing --- let us derive what it must be.
For `fibonacci-rec`, we only needed addition, and so were safely working over just monoid of addition over `ℕ`, and so the signature `ℕ → ℕ` was perfectly safe.
However, in `fibonacci-ext`, there are few new capabilities used.
1. To use subtraction, we must have an addition group.
2. To use exponentiation, we must have a multiplication monoid.
3. To use division by nonzero elements, we must have a multiplication group over nonzero elements.

(1.) and (2.) require that we have a (commutative) ring.
Then (3.) requires further that we have a field.
Since our result must eventually be reducible to a natural number,
the field to use should be the rational number field, `ℚ`.
Additionally since we are using `sqrt[5]` we must also extend `ℚ` with `sqrt[5]`, written `ℚ[sqrt[5]]`.
Since `sqrt[5]` is a zero of the `ℚ`-polynomial `X^2 - 5` (i.e. is algebraic), this is an algebraic field extension, which is a field itself.

So, we can type `fibonacci-ext` like so:

```agda
    fibonacci-ext : ℕ → ℚ[sqrt[5]]
    fibonacci-ext n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]
```

But how exactly is `ℚ[sqrt[5]]` defined in Agda?
First we formalize fields in Agda
(the Agda standard library only defines algebraic structures up to commutative rings and distributive lattices).
Then we formalize algebraic field extensions by a the square root of a square-free number.

## Fields

<!-- TODO -->

## Algebraic Field Extensions by Square Root of Square-Free Number

<!-- TODO -->


<!-- where `φ = (1/2)(1 + sqrt[5])` (the golden ratio). For the sake of simplicity, assume we are working with fixed-size numerical representations, so that addition, multiplication, and inversion are constant-time. Then this formula computes with the complexity of raising `φ` to the power `n`, which via recursive exponentiation involves `n` multiplications and so is `O(n)`. -->
