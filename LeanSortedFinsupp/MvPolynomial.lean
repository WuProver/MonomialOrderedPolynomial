import LeanSortedFinsupp.SortedAddMonoidAlgebra
import LeanSortedFinsupp.TreeRepr
import LeanSortedFinsupp.MonomialOrder

variable {σ} [DecidableEq σ] [LinearOrder σ] {R} [CommSemiring R] [DecidableEq R]

-- #synth AddCommMonoid <| Lex <| SortedFinsupp σ Nat compare

-- #synth DecidableEq <| Lex <| SortedFinsupp σ Nat compare


-- #synth Algebra R (SortedAddMonoidAlgebra R (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap))

def TreeRepr.toSortedAddMonoidAlgebra :
    TreeRepr σ R → SortedAddMonoidAlgebra R
      (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap)
  | const c => SortedAddMonoidAlgebra.single _ 0 c
  | var v => SortedAddMonoidAlgebra.single _ (SortedFinsupp.single _ v 1) 1
  | add p q => p.toSortedAddMonoidAlgebra + q.toSortedAddMonoidAlgebra
  | mul p q => p.toSortedAddMonoidAlgebra * q.toSortedAddMonoidAlgebra
  | pow p n => p.toSortedAddMonoidAlgebra ^ n
  | ref p => p.toSortedAddMonoidAlgebra

-- #check MvPolynomial.renameEquiv (SortedFinsupp.orderIsoFinsupp)
-- #check AddMonoidAlgebra.mapRangeAlgEquiv
-- #check AddMonoidAlgebra.domCongr

noncomputable def algEquivMvPolynomial :
    SortedAddMonoidAlgebra R
      (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap) ≃ₐ[R]
    (MvPolynomial σ R) :=
  AlgEquiv.trans SortedAddMonoidAlgebra.algEquivAddMonoidAlgebra
    (AddMonoidAlgebra.domCongr _ _ <| SortedFinsupp.lexAddEquiv compare)

lemma TreeRepr.algEquivMvPolynomial_apply
    {σ} [DecidableEq σ] [LinearOrder σ]
    (p : TreeRepr σ R) :
    algEquivMvPolynomial p.toSortedAddMonoidAlgebra = p.toMvPolynomial := by
  match p with
  | const c =>
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.equivFinsupp (.single _ (0 : SortedFinsupp σ Nat compare) c))
        = MvPolynomial.C c
    simp
    rfl
  | var v =>
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.equivFinsupp
          (.single _ (.single _ v 1 : SortedFinsupp σ Nat compare) 1))
        = MvPolynomial.X v
    simp
    convert_to
      AddMonoidAlgebra.single
        (SortedFinsupp.equivFinsupp <| SortedFinsupp.single _ v (1 : Nat)) (1 : R) =
      MvPolynomial.X v
    simp
    rfl
  | add p q => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p, TreeRepr.algEquivMvPolynomial_apply q]
  | mul p q => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p, TreeRepr.algEquivMvPolynomial_apply q]
  | pow p n => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p]
  | ref p => simp [TreeRepr.toSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p]

lemma TreeRepr.algEquivPolynomial_symm (p : TreeRepr σ R) :
    p.toSortedAddMonoidAlgebra = algEquivMvPolynomial.symm p.toMvPolynomial := by
  simp [← algEquivMvPolynomial_apply]

lemma MvPolynomial.PolyRepr.eq_iff {p q : MvPolynomial σ R}
    (p' : MvPolynomial.PolyRepr p) (q' : MvPolynomial.PolyRepr q) :
    p = q ↔ p'.tree.toSortedAddMonoidAlgebra = q'.tree.toSortedAddMonoidAlgebra := by
  simp [← p'.tree_eq, ← q'.tree_eq, ← TreeRepr.algEquivMvPolynomial_apply]

lemma MvPolynomial.PolyRepr.eq_iff' {p q : MvPolynomial σ R} [p' : MvPolynomial.PolyRepr p]
    [q' : MvPolynomial.PolyRepr q] :
    p = q ↔ p'.tree.toSortedAddMonoidAlgebra = q'.tree.toSortedAddMonoidAlgebra :=
  MvPolynomial.PolyRepr.eq_iff ..
