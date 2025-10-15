import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.MonomialOrder

namespace SortedAddMonoidAlgebra

variable {σ} [DecidableEq σ] [LinearOrder σ] {R} [CommSemiring R] [DecidableEq R]

noncomputable def algEquivMvPolynomial :
    SortedAddMonoidAlgebra R
      (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap) ≃ₐ[R]
    (MvPolynomial σ R) :=
  AlgEquiv.trans SortedAddMonoidAlgebra.algEquivAddMonoidAlgebra
    (AddMonoidAlgebra.domCongr _ _ <| SortedFinsupp.lexAddEquiv compare)

class _root_.MvPolynomial.SortedRepr (p : MvPolynomial σ R) where
  repr : SortedAddMonoidAlgebra R (Lex <| SortedFinsupp σ Nat compare) (compare · · |>.swap)
  eq : algEquivMvPolynomial repr = p

def _root_.MvPolynomial.toSortedRepr (p : MvPolynomial σ R) [inst : p.SortedRepr] := inst

open MvPolynomial

instance {c} : (C c : MvPolynomial σ R).SortedRepr where
  repr := SortedAddMonoidAlgebra.single _ 0 c
  eq := by
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.toFinsupp (.single _ (0 : SortedFinsupp σ Nat compare) c))
        = MvPolynomial.C c
    simp
    rfl

instance {v} : (X v : MvPolynomial σ R).SortedRepr where
  repr := SortedAddMonoidAlgebra.single _ (SortedFinsupp.single _ v 1) 1
  eq := by
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

instance (p q : MvPolynomial σ R) [p.SortedRepr] [q.SortedRepr] : (p * q).SortedRepr where
  repr := p.toSortedRepr.repr * q.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq, q.toSortedRepr.eq]

instance (p q : MvPolynomial σ R) [p.SortedRepr] [q.SortedRepr] : (p + q).SortedRepr where
  repr := p.toSortedRepr.repr + q.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq, q.toSortedRepr.eq]

instance {R} [CommRing R] [DecidableEq R] (p q : MvPolynomial σ R) [p.SortedRepr] [q.SortedRepr] :
    (p - q).SortedRepr where
  repr := p.toSortedRepr.repr - q.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq, q.toSortedRepr.eq]

instance {R} [CommRing R] [DecidableEq R] (p : MvPolynomial σ R) [p.SortedRepr] :
    (- p).SortedRepr where
  repr := - p.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq]

instance (p : MvPolynomial σ R) [p.SortedRepr] (n : ℕ) : (p ^ n).SortedRepr where
  repr := p.toSortedRepr.repr ^ n
  eq := by
    simp [p.toSortedRepr.eq]

instance (p : MvPolynomial σ R) [p.SortedRepr] (n : ℕ) : (n • p).SortedRepr where
  repr := n • p.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq]

instance {R} [CommRing R] [DecidableEq R] (p : MvPolynomial σ R) [p.SortedRepr] (n : ℤ) :
    (n • p).SortedRepr where
  repr := n • p.toSortedRepr.repr
  eq := by
    simp [p.toSortedRepr.eq]

instance : (0 : MvPolynomial σ R).SortedRepr where
  repr := 0
  eq := rfl

instance : (1 : MvPolynomial σ R).SortedRepr where
  repr := 1
  eq := by
    simp

instance {n : Nat} [Nat.AtLeastTwo n] : (ofNat(n) : MvPolynomial σ R).SortedRepr where
  repr := n
  eq := by
    simp
    rfl

lemma _root_.MvPolynomial.SortedRepr.eq_iff {p q : MvPolynomial σ R}
    (p' : MvPolynomial.SortedRepr p) (q' : MvPolynomial.SortedRepr q) :
    p = q ↔ p'.repr = q'.repr := by
  nth_rw 1 [← p'.eq, ← q'.eq]
  simp

lemma _root_.MvPolynomial.SortedRepr.eq_iff' {p q : MvPolynomial σ R}
    [p' : MvPolynomial.SortedRepr p] [q' : MvPolynomial.SortedRepr q] :
    p = q ↔ p'.repr = q'.repr := MvPolynomial.SortedRepr.eq_iff ..

instance {p q : MvPolynomial σ R} [p.SortedRepr] [q.SortedRepr] :
    Decidable (p = q) :=
  decidable_of_iff _ MvPolynomial.SortedRepr.eq_iff'.symm

open MonomialOrder

lemma _root_.MvPolynomial.SortedRepr.lex_degree_eq [WellFoundedGT σ] {p : MvPolynomial σ R}
    [p' : p.SortedRepr] :
    lex.degree p = SortedFinsupp.toFinsupp
      (ofLex (p'.repr.1.1.head?.elim (toLex 0) (·.1))) := sorry

lemma _root_.MvPolynomial.SortedRepr.lex_degree_eq' [WellFoundedGT σ] {p : MvPolynomial σ R}
    [p' : p.SortedRepr] :
    lex.toSyn (lex.degree p) = SortedFinsupp.orderIsoFinsupp
      (p'.repr.1.1.head?.elim (toLex 0) (·.1)) :=
  MvPolynomial.SortedRepr.lex_degree_eq
