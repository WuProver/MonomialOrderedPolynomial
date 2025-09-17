# MonomialOrderedPolynomial
This library provides a formally verified data structure for efficient polynomial identity testing via kernel reduction in Lean 4. By leveraging strictly ordered data structures, it ensures reliable in-kernel computation and verification of polynomial operations. Although primarily optimized for polynomial identity testing, the library also supports or plans to support a wide range of fundamental operations, including computing degrees, extracting coefficients, performing evaluations, and handling expansions of both univariate and multivariate polynomials across diverse contexts.

This project develops tools that help with the computation and formal verification of Gröbner bases of polynomial ideals. In addition, it supports other fundamental polynomial operations, including greatest common divisors, factorization, and solving polynomial systems. For the main Gröbner basis formalization effort, see: [WuProver/groebner_proj](https://github.com/WuProver/groebner_proj). This work is still in progress and under active development.

Both the library and its documents are still WIP.

## Introduction

### Main Contents

This library focusses on structure based on list where elements are sorted with an order.

- [`List.lean`](./MonomialOrderedPolynomial/List.lean): General operations and properties of such kind of structure.
- [`DSortedListMap.lean`](./MonoialOrderedPolynomial/DSortedFinsupp.lean): Maps based on sorted list.
- [`DSortedFinsupp.lean`](./MonomialOrderedPolynomial/DSortedFinsupp.lean): A sorted implementation of finitely-supported dependent functions [`DFinsupp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DFinsupp#doc) within the [Mathlib](https://github.com/leanprover-community/mathlib4). It is built upon the [`DSortedListMap`](./MonomialOrderedPolynomial/DSortedListMap.lean) data structure.
- [`SortedFinsupp.lean`](./MonomialOrderedPolynomial/SortedFinsupp.lean): A sorted implementation of finitely-supported functions [`Finsupp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Finsupp#doc) within the [Mathlib](https://github.com/leanprover-community/mathlib4).
- [`SortedAddMonoidAlgebra.lean`](./MonomialOrderedPolynomial/SortedAddMonoidAlgebra.lean): A sorted implementation of [`AddMonoidAlgebra`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AddMonoidAlgebra#doc) within the [Mathlib](https://github.com/leanprover-community/mathlib4).
- [`TreeRepr.lean`](./MonomialOrderedPolynomial/TreeRepr.lean): instances that extract a computable tree structure from concrete `Polynomial` and `MvPolynomial` expressions, inspired by [Junyan Xu's work on polynomial computations by reflection](https://gist.github.com/alreadydone/2dca4fde11fb2e9be7f8a10b59216b3f).
- [`Polynomial.lean`](./MonomialOrderedPolynomial/Polynomial.lean): equivalence of algebras from `SortedAddMonoidAlgebra` (where monomials are represented as sorted elements of a list) to [`Polynomial`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial#doc).
- [`MonomialOrder.lean`](./MonomialOrderedPolynomial/MonomialOrder.lean): Order on `SortedFinsupp`.
- [`MvPolynomial.Lean`](./MonomialOrderedPolynomial/MvPolynomial.lean): equivalence of algebras from `SortedAddMonoidAlgebra` to [`MvPolynomial`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MvPolynomial#doc).

### How It Works

At its core, this library enables computation through a technique known as proof by reflection. We establish a formal isomorphism, defining a two-way translation between incomputable mathematical objects from Mathlib and our computable data structures. This allows the kernel to efficiently reduce concrete expressions about structures we define, and prove proposition about the corresponding objects from Mathlib by the result, while guaranteeing mathematically sound and consistent with the original theory.

## Build
If you don't already have Lean 4 set up, please follow the official [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:
```bash
git clone https://github.com/WuProver/MonomialOrderedPolynomial.git
cd MonomialOrderedPolynomial
lake exe cache get
lake build
```

## Capabilities about `MvPolynomial` and `Polynomial`

This library provides support for operations of polynomials (`MvPolynomial` and `Polynomial`) on `SortedAddMonoidAlgebra`:

- const,
- variable,
- addition / subtraction,
- multiplication,
- exponentiation.

One of their applications is [PIT (polynomial identity testing)](https://en.m.wikipedia.org/wiki/Polynomial_identity_testing).

Corresponding `SortedAddMonoidAlgebra` of concrete polynomials can be synthesized via instance. Some examples are in [PolynomialExamples.lean](https://github.com/WuProver/MonomialOrderedPolynomial/blob/master/LeanSortedFinsupp/PolynomialExamlpes.lean).

### `Polynomial`-specific Operations

- Degree Computation: Calculation of polynomial degrees
- Coefficient Extraction: Retrieval of specific coefficients from polynomial expressions

### `MvPolynomial`-specific Operations

- Degree Computation (WIP): Calculation of polynomial degrees w.r.t. a specific monomial order (such as lexicographic order);
- Coefficient Extraction (WIP): Retrieval of specific coefficients from polynomial expressions w.r.t. a specific monomial order.

## Comparison on PIT

Our comparison is confined solely to polynomial operations within polynomial rings. Moreover, we only consider the case of processing a single goal or a single hypothesis.

### Comparison Table

| Goal | Requirement (Our Tool) | Requirement (Grind) | Notes & Implications |
| :--- | :--- | :--- | :--- |
| **Equality** | ✅ concrete polynomials with computable coefficients | ✅ provable by general properties of commutative semiring/ring | Our tool can prove polynomial with results of operations of coefficients, but only if they're computable and the polynomial is concrete. Grind is faster and may prove equality with unknown parts, while cannot use details except general properties of commutative semiring/ring. |
| **Disequality** | ✅ (same requirements as equality) | ❌ **Not Supported, except some trivial cases** | Grind can only prove two polynomials are equal, but it cannot prove they are not equal. |

### Some Examples
<!-- ![example](img/example.jpg) -->

#### `Polynomial`

`grind` doesn't solve the polynomial identity test below, since the coefficients are rational numbers:
```lean
example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
    grind  -- `grind` failed
```

our solution can prove the polynomial identity test below
```lean
example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
    rw [Polynomial.PolyRepr.eq_iff']
    decide +kernel
```

`grind` cannot determine if two polynomials are not equal
```lean
example : ((X + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
    grind  --`grind` failed
```

but our solution can do it
```lean
example : ((X + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
    simp +decide [Polynomial.PolyRepr.eq_iff']
```

#### `MvPolynomial`

Equality:
```lean
example : ((X 0 + X 1 + 1) ^ 10 : MvPolynomial Nat Nat) ≠ ((X 1 ^ 2 + 2 * X 1 +1) ^ 5) := by
  rw [ne_eq, MvPolynomial.PolyRepr.eq_iff']
  decide +kernel
```

Disequality:
```lean
example : ((X 0 + X 1) ^ 10 : MvPolynomial Nat Nat) = ((X 1 ^ 2 + 2 * X 0 * X 1 + X 0 ^ 2) ^ 5) := by
  rw [MvPolynomial.PolyRepr.eq_iff']
  decide +kernel
```



### Conclusion
Our tool is particularly suitable for polynomial manipulation, with an emphasis on Gröbner basis computation and verification, as well as on operations such as computing polynomial degrees and coefficients



## WIP
1. Implement monomial order on `SortedFinsupp`, to imolement sorted `MvPolynomial`;
2. refactor `SortedFinsupp` to use independent `Prod` to be more effective.
