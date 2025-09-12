# MonomialOrderedPolynomial
This library provides a formally verified data structure for efficient polynomial identity testing via kernel reduction in Lean 4. By leveraging strictly ordered data structures, it ensures reliable in-kernel computation and verification of polynomial operations. Although primarily optimized for polynomial identity testing, the library also supports a wide range of fundamental operations, including computing degrees, extracting coefficients, performing evaluations, and handling expansions of both univariate and multivariate polynomials across diverse contexts.

This project develops tools that help with the computation and formal verification of Gröbner bases of polynomial ideals. In addition, it supports other fundamental polynomial operations, including greatest common divisors, factorization, and solving polynomial systems. For the main Gröbner basis formalization effort, see: [WuProver/groebner_proj](https://github.com/WuProver/groebner_proj). This work is still in progress and under active development.

## Introduction

### Main Structure
- [`DSortedFinsupp`](https://github.com/WuProver/SortedPolynomial/blob/master/LeanSortedFinsupp/DSortedFinsupp.lean): A sorted implementation of finitely-supported dependent functions [`DFinsupp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/DFinsupp/Defs.html#DFinsupp) within the [Mathlib](https://github.com/leanprover-community/mathlib4). It is built upon the [`DSortedListMap`](https://github.com/WuProver/SortedPolynomial/blob/master/LeanSortedFinsupp/DSortedListMap.lean) data structure.
- [`SortedFinsupp`](https://github.com/WuProver/SortedPolynomial/blob/master/LeanSortedFinsupp/SortedFinsupp.lean): A sorted implementation of finitely-supported functions [`Finsupp`](leanprover-community.github.io/mathlib4_docs/find/?pattern=Finsupp#doc) within the [Mathlib](https://github.com/leanprover-community/mathlib4).
- [`SortedAddMonoidAlgebra`](https://github.com/WuProver/SortedPolynomial/blob/master/LeanSortedFinsupp/SortedAddMonoidAlgebra.lean): A sorted implementation of [`AddMonoidAlgebra`](https://leanprover-community.github.io/mathlib4_docs/search.html?q=AddMonoidAlgebra) within the [Mathlib](https://github.com/leanprover-community/mathlib4).

### How It Works
At its core, this library enables computation through a technique known as proof by reflection. We establish a formal isomorphism, defining a two-way translation between abstract mathematical objects from Mathlib (such as `Polynomial` expressions with concrete coefficients) and our internal, computable data structures (like sorted lists). This allows the kernel to efficiently reduce expressions within our framework, while guaranteeing that the results remain mathematically sound and consistent with the original abstract theory.

## Build
If you don't already have Lean 4 set up, please follow the official [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:
```bash
git clone https://github.com/WuProver/MonomialOrderedPolynomial.git
cd MonomialOrderedPolynomial
lake exe cache get!
lake build
```

## Comparison

### Core Comparison Table

| Feature | Our Tool | Grind | Notes & Implications |
| :--- | :--- | :--- | :--- |
| **Equality** | ✅ Supported | ✅ Supported | |
| **Inequality** | ✅ Supported | ❌ **Not Supported** | **Major Limitation:**  Grind provides no way to check if values are not equal. |
| **Coeffcients** | ✅ Fully Supported | ❌ **Only Int** | Grind can only determine the equality of polynomials with integer coefficients |

### Conclusion
Use the right tool for the job. Our tool is more suitable for polynomial manipulation, general computations.

## ToDo
1. Implement monomial order on `SortedFinsupp`, to imolement sorted `MvPolynomial`;
2. refactor `SortedFinsupp` to use independent `Prod` to be more effective.
