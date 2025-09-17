import LeanSortedFinsupp.TreeRepr
import LeanSortedFinsupp.SortedAddMonoidAlgebra
import LeanSortedFinsupp.Ordering

section Polynomial

variable {R} [CommSemiring R] [DecidableEq R]
open SortedAddMonoidAlgebra

#check Nat.compare_eq_ite_le

instance : Fact <| ∀ (a i j : Nat), (compare i j).swap = (compare (a + i) (a + j)).swap := ⟨
  by
    simp [Nat.compare_eq_ite_le]
⟩

set_option trace.Meta.synthInstance true in
-- open Classical in
#synth Algebra R (SortedAddMonoidAlgebra R Nat (compare · · |>.swap))

def TreeRepr.toSortedAddMonoidAlgebra :
    TreeRepr Unit R → SortedAddMonoidAlgebra R Nat (compare · · |>.swap)
  | const c => single _ 0 c
  | var _ => single _ 1 1
  | add p q => p.toSortedAddMonoidAlgebra + q.toSortedAddMonoidAlgebra
  | mul p q => p.toSortedAddMonoidAlgebra * q.toSortedAddMonoidAlgebra
  | pow p n => p.toSortedAddMonoidAlgebra ^ n
  | ref p => p.toSortedAddMonoidAlgebra

def algEquivPolynomial :
    (SortedAddMonoidAlgebra R Nat (compare · · |>.swap)) ≃ₐ[R] (Polynomial R) :=
  AlgEquiv.trans SortedAddMonoidAlgebra.algEquivAddMonoidAlgebra (Polynomial.toFinsuppIsoAlg R).symm

lemma TreeRepr.algEquivPolynomial_apply (p : TreeRepr Unit R) :
    algEquivPolynomial p.toSortedAddMonoidAlgebra = p.toPolynomial := by
  match p with
  | const c =>
    simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial, algEquivPolynomial]
    convert_to (Polynomial.toFinsuppIsoAlg R).symm (Finsupp.single 0 c) = _
    · rw [AlgEquiv.symm_apply_eq]
      simp [algEquivAddMonoidAlgebra, ringEquivAddMonoidAlgebra]
      ext
      simp [Finsupp.single_apply]
    · simp [AlgEquiv.symm_apply_eq]
  | var _ =>
    simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial, algEquivPolynomial]
    convert_to (Polynomial.toFinsuppIsoAlg R).symm (Finsupp.single 1 1) = _
    · rw [AlgEquiv.symm_apply_eq]
      simp [algEquivAddMonoidAlgebra, ringEquivAddMonoidAlgebra]
      ext
      simp [Finsupp.single_apply]
    · simp [AlgEquiv.symm_apply_eq]
  | add p q => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial,
    TreeRepr.algEquivPolynomial_apply p, TreeRepr.algEquivPolynomial_apply q]
  | mul p q => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial,
    TreeRepr.algEquivPolynomial_apply p, TreeRepr.algEquivPolynomial_apply q]
  | pow p n => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial,
    TreeRepr.algEquivPolynomial_apply p]
  | ref p => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toPolynomial,
    TreeRepr.algEquivPolynomial_apply p]

lemma TreeRepr.algEquivPolynomial_symm (p : TreeRepr Unit R) :
    p.toSortedAddMonoidAlgebra = algEquivPolynomial.symm p.toPolynomial := by
  simp [← algEquivPolynomial_apply]

lemma Polynomial.PolyRepr.eq_iff {p q : Polynomial R} (p' : Polynomial.PolyRepr p) (q' : Polynomial.PolyRepr q) :
    p = q ↔ p'.tree.toSortedAddMonoidAlgebra = q'.tree.toSortedAddMonoidAlgebra := by
  simp [← p'.tree_eq, ← q'.tree_eq, ← TreeRepr.algEquivPolynomial_apply]

lemma Polynomial.PolyRepr.eq_iff' {p q : Polynomial R} [p' : Polynomial.PolyRepr p] [q' : Polynomial.PolyRepr q] :
    p = q ↔ p'.tree.toSortedAddMonoidAlgebra = q'.tree.toSortedAddMonoidAlgebra :=
  Polynomial.PolyRepr.eq_iff ..

lemma Polynomial.PolyRepr.degree_eq {p : Polynomial R} [p' : Polynomial.PolyRepr p] :
    p.degree = p'.tree.toSortedAddMonoidAlgebra.val.val.head?.elim ⊥ (·.1) := by
  sorry

lemma Polynomial.PolyRepr.leadingCoeff {p : Polynomial R} [p' : Polynomial.PolyRepr p] :
    p.leadingCoeff = p'.tree.toSortedAddMonoidAlgebra.val.val.head?.elim 0 (·.2) := by
  sorry

lemma Polynomial.PolyRepr.coeff {p : Polynomial R} {n} [p' : Polynomial.PolyRepr p] :
    p.coeff n = p'.tree.toSortedAddMonoidAlgebra n := by
  sorry

end Polynomial
