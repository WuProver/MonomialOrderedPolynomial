import LeanSortedFinsupp.Polynomial

open Polynomial

set_option profiler true
example : ((X  + 1) ^ 20 : Nat[X]) = ((X ^ 2 + 2 * X + 1) ^ 10: Nat[X]) := by
  grind
  -- rw [Polynomial.PolyRepr.eq_iff']
  -- decide +kernel

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  intro h
  rw [Polynomial.PolyRepr.eq_iff'] at h
  simp +decide at h

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  rw [ne_eq, Polynomial.PolyRepr.eq_iff']
  simp +decide

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  simp +decide [Polynomial.PolyRepr.eq_iff']

example : ((X  + 1) ^ 20 : Nat[X]) ≠ ((X ^ 2 + 2 * X +1) ^ 10: Nat[X]) + 1 := by
  fail_if_success grind
  sorry

example {x : Nat} : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  grind

example {p} :
    ((X + p) ^ 2 : ℚ[X]) = ((X ^ 2 + 2 * X * p + p ^ 2) : ℚ[X]) := by
  -- our solution cannot prove it (with unknown p)
  grind

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
  -- `grind` doesn't solve, since it doesn't know Polynomial.C
  fail_if_success grind
  sorry

example : ((X + C (1 / 2 : ℚ)) ^ 2 : ℚ[X]) = ((X ^ 2 + X + C (1 / 4 : ℚ))) := by
  rw [Polynomial.PolyRepr.eq_iff']
  decide +kernel

example : ((X ^ 3 + 1) ^ 3 : ℚ[X]).degree = 9 := by
  compute_degree
  simp
  rfl
  rfl

example : (((X + C (1 / 2 : ℚ)) ^ 3 : ℚ[X]) - X ^ 3).leadingCoeff = (3 / 2 : ℚ) := by
  rw [Polynomial.PolyRepr.leadingCoeff]
  decide +kernel

example : (((X + C (1 / 2 : ℚ)) ^ 3 : ℚ[X]) - X ^ 3).coeff 1 = (3 / 4 : ℚ) := by
  rw [Polynomial.PolyRepr.coeff]
  decide +kernel

example : ((X + C (1 / 2 : ℝ)) ^ 2 : ℝ[X]) = ((X ^ 2 + X + C (1 / 4 : ℝ))) := by
  -- todo
  -- can be proved via homomorphism from ℚ to ℝ
  sorry

