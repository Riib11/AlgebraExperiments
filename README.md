# README

## Module Organization 

```
ExtensionFibonacci.agda       # closed-form fibonacci implementation

Algebra/
	Field/
		Base.agda              # formalization of mathematical field
		Rational.agda          # instantiation of the rational field
		Extension/BySqrt.agda  # algebraic extension by posited square root

Data/
	Subset.agda                # data type of A-terms that satisfy A-predicate
```

## Extension Fibonacci

This module implements a function `fibonacci : (n : ℕ) → ℕ` which computes the `n`th Fibonacci number using the closed formula.


### Fibonacci via Recursive Formula

A common implementation of this is the following recursive function:

	fibonacci-rec 0 = 0
	fibonacci-rec 1 = 1
	fibonacci-rec (suc (suc n)) = ficonacci-rec (suc n) + fibonacci-rec n

For the sake of simplicity, assume we are working with fixed-size numerical representations, so that addition and multiplication are constant-time. Each recursive call spawns 2 further calls, and the max call depth is `n`, so the resulting binary recursion-tree has height `n` (though all but one of the root-to-leaf-paths have length less than `n`). For a binary tree of height `n`, the number of nodes in the tree is less than `2^n`. So, the time complexity of `fibonacci-rec` is `O(log[2^n])`.


### Fibonacci via Closed Formula over ℚ[sqrt[5]]

This module's implementation instead uses the closed formula

	fibonacci-ext n = (φ ^ n - (1 - φ) ^ n) / sqrt[5]

where `φ = (1/2)(1 + sqrt[5])` (the golden ratio). For the sake of simplicity, assume we are working with fixed-size numerical representations, so that addition, multiplication, and inversion are constant-time. Then this formula computes with the complexity of raising `φ` to the power `n`, which via recursive exponentiation involves `n` multiplications and so is `O(n)`.
