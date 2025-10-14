import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.TreeRepr
import MonomialOrderedPolynomial.MonomialOrder

variable {σ} [DecidableEq σ] [LinearOrder σ] {R} [CommSemiring R] [DecidableEq R]

-- #synth AddCommMonoid <| Lex <| SortedFinsupp σ Nat compare

-- #synth DecidableEq <| Lex <| SortedFinsupp σ Nat compare


-- #synth Algebra R (SortedAddMonoidAlgebra R (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap))

def TreeRepr.toMvSortedAddMonoidAlgebra :
    TreeRepr σ R → SortedAddMonoidAlgebra R
      (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap)
  | const c => SortedAddMonoidAlgebra.single _ 0 c
  | var v => SortedAddMonoidAlgebra.single _ (SortedFinsupp.single _ v 1) 1
  | add p q => p.toMvSortedAddMonoidAlgebra + q.toMvSortedAddMonoidAlgebra
  | mul p q => p.toMvSortedAddMonoidAlgebra * q.toMvSortedAddMonoidAlgebra
  | pow p n => p.toMvSortedAddMonoidAlgebra ^ n
  | ref p => p.toMvSortedAddMonoidAlgebra

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
    algEquivMvPolynomial p.toMvSortedAddMonoidAlgebra = p.toMvPolynomial := by
  match p with
  | const c =>
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.toFinsupp (.single _ (0 : SortedFinsupp σ Nat compare) c))
        = MvPolynomial.C c
    simp
    rfl
  | var v =>
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.toFinsupp
          (.single _ (.single _ v 1 : SortedFinsupp σ Nat compare) 1))
        = MvPolynomial.X v
    simp
    convert_to
      AddMonoidAlgebra.single
        (SortedFinsupp.toFinsupp <| SortedFinsupp.single _ v (1 : Nat)) (1 : R) =
      MvPolynomial.X v
    simp
    rfl
  | add p q => simp [TreeRepr.toMvSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p, TreeRepr.algEquivMvPolynomial_apply q]
  | mul p q => simp [TreeRepr.toMvSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p, TreeRepr.algEquivMvPolynomial_apply q]
  | pow p n => simp [TreeRepr.toMvSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p]
  | ref p => simp [TreeRepr.toMvSortedAddMonoidAlgebra, TreeRepr.toMvPolynomial,
      TreeRepr.algEquivMvPolynomial_apply p]

lemma TreeRepr.algEquivMvPolynomial_symm (p : TreeRepr σ R) :
    p.toMvSortedAddMonoidAlgebra = algEquivMvPolynomial.symm p.toMvPolynomial := by
  simp [← algEquivMvPolynomial_apply]

lemma MvPolynomial.PolyRepr.eq_iff {p q : MvPolynomial σ R}
    (p' : MvPolynomial.PolyRepr p) (q' : MvPolynomial.PolyRepr q) :
    p = q ↔ p'.tree.toMvSortedAddMonoidAlgebra = q'.tree.toMvSortedAddMonoidAlgebra := by
  simp [← p'.tree_eq, ← q'.tree_eq, ← TreeRepr.algEquivMvPolynomial_apply]

lemma MvPolynomial.PolyRepr.eq_iff' {p q : MvPolynomial σ R} [p' : MvPolynomial.PolyRepr p]
    [q' : MvPolynomial.PolyRepr q] :
    p = q ↔ p'.tree.toMvSortedAddMonoidAlgebra = q'.tree.toMvSortedAddMonoidAlgebra :=
  MvPolynomial.PolyRepr.eq_iff ..

open MonomialOrder

lemma MvPolynomial.PolyRepr.lex_degree_eq [WellFoundedGT σ] {p : MvPolynomial σ R}
    [p' : MvPolynomial.PolyRepr p] :
    lex.degree p = SortedFinsupp.toFinsupp
      (ofLex (p'.tree.toMvSortedAddMonoidAlgebra.1.1.head?.elim (toLex 0) (·.1))) := sorry

lemma MvPolynomial.PolyRepr.lex_degree_eq' [WellFoundedGT σ] {p : MvPolynomial σ R}
    [p' : MvPolynomial.PolyRepr p] :
    lex.toSyn (lex.degree p) = SortedFinsupp.orderIsoFinsupp
      (p'.tree.toMvSortedAddMonoidAlgebra.1.1.head?.elim (toLex 0) (·.1)) :=
  MvPolynomial.PolyRepr.lex_degree_eq
