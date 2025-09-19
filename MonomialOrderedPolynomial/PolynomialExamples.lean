import MonomialOrderedPolynomial.Polynomial

open Polynomial

set_option profiler true

section PIT

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  intro h
  rw [Polynomial.PolyRepr.eq_iff'] at h
  simp +decide at h

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  rw [ne_eq, Polynomial.PolyRepr.eq_iff']
  simp +decide

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  simp +decide [Polynomial.PolyRepr.eq_iff']

example :
    ((X + (1 / 2 : ℚ[X])) ^ 2 : ℚ[X]) = ((X ^ 2 + X + (1 / 4 : ℚ[X])) : ℚ[X]) := by
  convert_to ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ)) : ℚ[X])
  · congr
    simp
    convert Polynomial.div_C
    simp
  · congr
    simp
    convert Polynomial.div_C
    simp
  · rw [Polynomial.PolyRepr.eq_iff']
    decide +kernel

example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
  rw [Polynomial.PolyRepr.eq_iff']
  decide +kernel

example : ((X + C (1 / 2 : ℝ)) ^ 2 : ℝ[X]) = ((X ^ 2 + X + C (1 / 4 : ℝ))) := by
  -- todo
  -- can be proved via homomorphism from ℚ to ℝ
  sorry

example : ((X + C (1 / 2 : ℝ)) ^ 2 : ℝ[X]) ≠ ((X ^ 2 + X + C (1 / 4 : ℝ))) + 1 := by
  -- todo
  -- can be proved via embedding from ℚ to ℝ
  sorry

end PIT

section DegreeAndCoeff

-- compare with `compute_degree`

-- tactic `compute_degree` in Mathlib:
-- https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/All-tactics/#compute_degree-next
-- it can prove results about a polynomial with incomputable coefficients and/or even unknown subterms
example {c : ℝ} : ((X ^ 3 + C c) ^ 3 : ℝ[X]).degree = 9 := by
  compute_degree <;> aesop

-- set_option maxRecDepth 10000
example {c : Int} : ((X ^ 3 + C c) : Int[X]).degree = 3 := by
  rw [Polynomial.PolyRepr.degree_eq]
  -- our tools cannot solve it with unknown `c` (dependence on hypothesis `c`)
  sorry

example {c : ℝ} : ((X ^ 3 + C c) ^ 3 : ℝ[X]).degree = 9 := by
  rw [Polynomial.PolyRepr.degree_eq]
  -- cannot solve it with "incomputable" coefficients
  -- todo: solve with embedding from ℚ to ℝ
  sorry

-- with computable coefficient
example : ((X ^ 3 + C 1) ^ 3 : Int[X]).degree = 9 := by
  compute_degree <;> decide

-- `compute_degree` doesn't work when the leading term of a subterm is eliminated
example : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree = 6 := by
  compute_degree
  · -- `False` to be proved
    sorry
  · sorry
  · sorry
  · sorry
  · sorry

example : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree = 6 := by
  rw [Polynomial.PolyRepr.degree_eq]
  decide +kernel

example : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree ^ 2 = 36 := by
  rw [Polynomial.PolyRepr.degree_eq]
  decide +kernel

example : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree ^ 2 = 36 := by
  have : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree = (?_ : WithBot Nat) := by
    rw [Polynomial.PolyRepr.degree_eq]
    reduce
    -- convert_to some 6 = (6 : WithBot Nat) -- optional
    exact rfl
  -- now we have `this : ((X ^ 3 + C 1) ^ 3 - X ^ 9: Int[X]).degree = 6`
  rw [this]
  rfl

example : (((X + C (1 / 2 : ℚ)) ^ 3 : ℚ[X]) - X ^ 3).leadingCoeff = (3 / 2 : ℚ) := by
  rw [Polynomial.PolyRepr.leadingCoeff]
  decide +kernel

example : (((X + C (1 / 2 : ℚ)) ^ 3 : ℚ[X]) - X ^ 3).coeff 1 = (3 / 4 : ℚ) := by
  rw [Polynomial.PolyRepr.coeff]
  decide +kernel

end DegreeAndCoeff

/- examples in README -/
section ExamplesInReadme

/-
`grind` doesn't solve the polynomial identity test below, since the coefficients are rational
numbers and it doesn't know `Polynomial.C`:
-/
open Polynomial in
example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
  fail_if_success grind  -- `grind` failed
  sorry

/-
We can prove the polynomial identity below
-/
open Polynomial in
example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
  rw [Polynomial.PolyRepr.eq_iff']
  decide +kernel

/-
`grind` cannot determine if two polynomials are not equal
-/
open Polynomial in
example : ((X + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  fail_if_success grind  --`grind` failed
  sorry

/-
We can prove  two polynomials are not equal  
-/
open Polynomial in
example : ((X + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  simp +decide [Polynomial.PolyRepr.eq_iff']

/-
grind can prove some goals dependent on hypotheses, including but not limited to abstract algebra
structures, unknown polynomials, and equations.
-/
open Polynomial in
example {R : Type*} [CommRing R] (p : Polynomial R) : p + 1 + X = 1 + p + X := by
  grind

open Polynomial in
example {R : Type*} [CommRing R] (p q : Polynomial R) (h : p + 1 = q) :
    p ^ 2 - 1 + Polynomial.X = q ^ 2 - 2 * q + Polynomial.X := by
  grind

/-
but not our tools
-/
open Polynomial in
example {R : Type*} [CommRing R] [DecidableEq R] :
    1 + X = (X + 1 : R[X]) := by
  rw [Polynomial.PolyRepr.eq_iff']
  fail_if_success decide +kernel -- failed: `Expected type must not contain free variables`
  fail_if_success decide +kernel +revert --failed: `failed to synthesize`
  sorry

open Polynomial in
example (p : Polynomial Int) :
    1 + p = (p + 1 : Int[X]) := by
  fail_if_success { rw [Polynomial.PolyRepr.eq_iff'] } -- failed: `failed to synthesize`
  sorry

end ExamplesInReadme
