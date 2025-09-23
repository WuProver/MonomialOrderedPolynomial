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

open MonomialOrder in
example :
    lex.degree (X 1 + X 2 : MvPolynomial (Fin 2) Int) ≼[lex]
      lex.degree (X 0 + X 1 ^ 2: MvPolynomial (Fin 2) Int) := by
  rw [MvPolynomial.PolyRepr.lex_degree_eq', MvPolynomial.PolyRepr.lex_degree_eq',
    SortedFinsupp.orderIsoFinsupp.le_iff_le, ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
  decide +kernel
