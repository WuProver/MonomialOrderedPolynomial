import MonomialOrderedPolynomial.SortedAddMonoidAlgebra
import MonomialOrderedPolynomial.MonomialOrder
import MonomialOrderedPolynomial.Finsupp
import Groebner.Defs

namespace SortedAddMonoidAlgebra

variable {σ} [LinearOrder σ] {R} [CommSemiring R] [DecidableEq R]

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

instance {c : R} {s : σ →₀ ℕ} [inst : s.SortedRepr] :
    (MvPolynomial.monomial s c).SortedRepr where
  repr := SortedAddMonoidAlgebra.single _ inst.repr c
  eq := by
    convert_to
      (AddMonoidAlgebra.domCongr R R (SortedFinsupp.lexAddEquiv compare))
        (SortedFinsupp.toFinsupp
          (.single _ inst.repr c))
        = MvPolynomial.monomial _ _
    simp
    congr
    exact inst.eq

lemma _root_.MvPolynomial.SortedRepr.coeff_eq (p : MvPolynomial σ R) [inst : p.SortedRepr] (c : σ →₀ ℕ) :
    p.coeff c = inst.repr (SortedFinsupp.lexAddEquiv compare |>.symm c) := by
  simp [coeff, ← inst.eq, algEquivMvPolynomial]
  rw (config := {transparency := .default}) [AddMonoidAlgebra.domCongr_apply]

lemma _root_.MvPolynomial.SortedRepr.support_eq (p : MvPolynomial σ R) [inst : p.SortedRepr]  :
    p.support = p.toSortedRepr.repr.support.toFinset.map (SortedFinsupp.lexAddEquiv (σ := σ) (R := Nat) compare) := by
  ext x
  simp [MvPolynomial.SortedRepr.coeff_eq, SortedFinsupp.mem_support_iff]

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

section MonomialOrder
open MonomialOrder

variable {p q : MvPolynomial σ R}
  [p' : p.SortedRepr] [q' : q.SortedRepr]

variable [WellFoundedGT σ]

instance {α} [LinearOrder α] : IsTotal (α := α) GE.ge where
  total := by simp [LinearOrder.le_total]

-- lemma _root_.MvPolynomial.SortedRepr.repr_support_eq :
--   p.toSortedRepr.repr.support =
--     ((p.support.map (lex (σ := σ) |>.toSyn).toEmbedding).sort GE.ge).map
--     (SortedFinsupp.lexAddEquiv compare).symm := sorry

lemma _root_.Finset.map_sort_ge_head?_getD_bot (α : Type*) [LinearOrder α] [OrderBot α]
    (s : List α) (hs : s.Sorted GE.ge) : s.head?.getD ⊥ = s.toFinset.sup id := by
  cases s
  · simp
  · simp
    intro b hb
    aesop

lemma _root_.MvPolynomial.SortedRepr.lex_degree_eq :
    lex.degree p = ofLex (SortedFinsupp.lexOrderIsoLexFinsupp (p'.repr.support.head?.getD ⊥)) := by
  rw [Finset.map_sort_ge_head?_getD_bot, degree, MvPolynomial.SortedRepr.support_eq]
  · simp; rfl
  rw [List.Sorted, List.pairwise_iff_forall_sublist]
  have := (SortedRepr.repr p).support_pairwise
  simp [List.pairwise_iff_forall_sublist] at this
  intro a b h
  replace this := this a b h
  rw [compare_gt_iff_gt] at this
  apply le_of_lt at this
  exact this

-- todo: optimization
lemma _root_.MvPolynomial.SortedRepr.lex_leadingCoeff_eq :
    lex.leadingCoeff p = p'.repr (p'.repr.support.head?.getD ⊥) := by
  classical
  simp [leadingCoeff, MvPolynomial.SortedRepr.lex_degree_eq,
    MvPolynomial.SortedRepr.coeff_eq]
  congr
  convert_to (SortedFinsupp.lexAddEquiv compare).symm (SortedFinsupp.lexAddEquiv compare _) = _
  · intro _
    exact Classical.decEq ..
  exact AddEquiv.symm_apply_apply (SortedFinsupp.lexAddEquiv compare) ((SortedFinsupp.support (SortedRepr.repr p)).head?.getD ⊥)

lemma _root_.MvPolynomial.SortedRepr.lex_degree_eq' :
    lex.toSyn (lex.degree p) =
      SortedFinsupp.lexOrderIsoLexFinsupp (p'.repr.support.head?.getD ⊥) :=
  MvPolynomial.SortedRepr.lex_degree_eq

instance : (lex.degree p).SortedRepr where
  repr := ofLex <| p'.repr.support.head?.getD ⊥
  eq := by
    simp [p'.lex_degree_eq]
    rfl

instance {R} [CommRing R] [DecidableEq R] [WellFoundedGT σ] {p q : MvPolynomial σ R}
  [p' : p.SortedRepr] [q' : q.SortedRepr] : (lex.sPolynomial p q).SortedRepr where
  repr :=
    ((monomial (lex.degree q - lex.degree p)) (q'.repr (q'.repr.support.head?.getD ⊥)) * p -
      (monomial (lex.degree p - lex.degree q)) (p'.repr (p'.repr.support.head?.getD ⊥)) * q).toSortedRepr.repr
  eq := by
    rw [SortedRepr.eq, ← SortedRepr.lex_leadingCoeff_eq, ← SortedRepr.lex_leadingCoeff_eq]
    rfl
