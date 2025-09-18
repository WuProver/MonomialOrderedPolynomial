import MonomialOrderedPolynomial.MvPolynomial

open MvPolynomial

lemma example1 : (X 0 + 1 : MvPolynomial Nat Int) ^ 20 =
    (X 0 ^ 2 + X 0 + X 0 + 1 : MvPolynomial Nat Int) ^ 10 := by
  rw [MvPolynomial.PolyRepr.eq_iff']
  decide +kernel

#print axioms example1

example : ((X 0 + X 1 + 1) ^ 10 : MvPolynomial Nat Nat) ≠ ((X 1 ^ 2 + 2 * X 1 +1) ^ 5) := by
  rw [ne_eq, MvPolynomial.PolyRepr.eq_iff']
  decide +kernel

example : ((X () + 1) ^ 10 : MvPolynomial Unit Nat) ≠ ((X 1 ^ 2 + 2 * X 1 +1) ^ 5) + 1 := by
  rw [ne_eq, MvPolynomial.PolyRepr.eq_iff']
  decide +kernel

example : ((X 0 + X 1) ^ 10 : MvPolynomial Nat Nat) = ((X 1 ^ 2 + 2 * X 0 * X 1 +X 0  ^ 2) ^ 5) := by
  rw [MvPolynomial.PolyRepr.eq_iff']
  decide +kernel

example : ((X 0 + X 1) ^ 10 : MvPolynomial Nat Nat) = ((X 1 ^ 2 + 2 * X 0 * X 1 + X 0 ^ 2) ^ 5) := by
  rw [MvPolynomial.PolyRepr.eq_iff']
  decide +kernel

example : (1 : Polynomial Int) ≠ (0 : Polynomial Int) := by grind

example :
    (Polynomial.X + 1 : Polynomial Int) ^ 2 ≠ Polynomial.X ^ 2 + 2 * Polynomial.X + 4:= by
  grind

example :
    (Polynomial.X + 1 : Polynomial Int) ^ 2 ≠ Polynomial.X ^ 2 + 3 * Polynomial.X := by
  fail_if_success grind


example {R : Type*} [CommRing R] (p : Polynomial R) : p + 1 + Polynomial.X = 1 + p + Polynomial.X := by
  fail_if_success rw [Polynomial.PolyRepr.eq_iff']
  sorry

example {R : Type*} [CommRing R] (p q : Polynomial R) (h : p + 1 = q) :
    p ^ 2 - 1 + Polynomial.X = q ^ 2 - 2 * q + Polynomial.X := by
  grind

example {R : Type*} [CommRing R] (p q : Polynomial R) (h : p + 1 = q) :
    p ^ 2 - 1 + Polynomial.X = q ^ 2 - 2 * q + Polynomial.X := by
  fail_if_success rw [Polynomial.PolyRepr.eq_iff']
  sorry
