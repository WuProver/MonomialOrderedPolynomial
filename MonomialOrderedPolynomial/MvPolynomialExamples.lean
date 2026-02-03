import MonomialOrderedPolynomial.MvPolynomial
import Groebner.Groebner
import Groebner.ToMathlib.List

open MvPolynomial MonomialOrder

lemma example1 : (X 0 + 1 : MvPolynomial Nat Int) ^ 20 =
    (X 0 ^ 2 + X 0 + X 0 + 1 : MvPolynomial Nat Int) ^ 10 := by
  rw [MvPolynomial.SortedRepr.eq_iff']
  decide +kernel

set_option profiler true

lemma example2 : ((X 0 + X 1 + 1) ^ 10 : MvPolynomial Nat Nat) ≠ ((X 1 ^ 2 + 2 * X 1 +1) ^ 5) := by
  decide +kernel

#print axioms example2

lemma example3 : ((X () + 1) ^ 10 : MvPolynomial Unit Nat) ≠ ((X 1 ^ 2 + 2 * X 1 +1) ^ 5) + 1 := by
  decide +kernel

#print axioms example3

lemma example4 : ((X 0 + X 1) ^ 10 : MvPolynomial Nat Nat) = ((X 1 ^ 2 + 2 * X 0 * X 1 +X 0  ^ 2) ^ 5) := by
  decide +kernel

#print axioms example4

lemma example5 : ((X 0 + X 1) ^ 10 : MvPolynomial Nat Nat) = ((X 1 ^ 2 + 2 * X 0 * X 1 + X 0 ^ 2) ^ 5) := by
  decide +kernel

#print axioms example5

open MonomialOrder in
lemma example6 :
    lex.degree (X 1 + X 2 : MvPolynomial (Fin 2) Int) ≼[lex]
      lex.degree (X 0 + X 1 ^ 2: MvPolynomial (Fin 2) Int) := by
  rw [MvPolynomial.SortedRepr.lex_degree_eq', MvPolynomial.SortedRepr.lex_degree_eq',
    SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le, ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)]
  decide +kernel

lemma withBotDegree_le_of_repr_le {σ R} [LinearOrder σ] [CommSemiring R]
    [DecidableEq R] [WellFoundedGT σ]
    {p q r : MvPolynomial σ R} [inst_p : p.SortedRepr]
    [inst_q : q.SortedRepr] [inst_r : r.SortedRepr] :
    (show WithBot <| Lex (SortedFinsupp σ ℕ compare) from inst_p.repr.support.head?)
    + (show WithBot <| Lex (SortedFinsupp σ ℕ compare) from inst_q.repr.support.head?)
      ≤ inst_r.repr.support.head? →
    lex.toWithBotSyn (lex.withBotDegree p) +
    lex.toWithBotSyn (lex.withBotDegree q) ≤ lex.toWithBotSyn (lex.withBotDegree r)  := by
  intro h
  rw [MvPolynomial.SortedRepr.lex_withBotDegree_eq',
    MvPolynomial.SortedRepr.lex_withBotDegree_eq',
    MvPolynomial.SortedRepr.lex_withBotDegree_eq'
    -- SortedFinsupp.lexOrderIsoLexFinsupp.le_iff_le,
    -- ← Std.LawfulLECmp.isLE_iff_le (cmp := compare)
  ]
  rwa [← WithBot.map_add', WithBot.map_le_iff]
  · simp
  simp [SortedFinsupp.lexOrderIsoLexFinsupp]

lemma example7 :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 4) ℚ)
      {X 0, X 1, X 2, X 3} 0 := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [IsRemainder.isRemainder_range_fintype, ← exists_and_right]
  /- todo: optimization: it is possible to provide their computable representation instead of
  synthesized from `MvPolynomial`. -/
  use [X 0, X 1 ^ 2, X 2 ^ 3, X 3 ^ 4].get
  split_ands
  · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    all_goals decide +kernel-- PIT, proof by reflection
  · intro i
    fin_cases i
    all_goals {
      -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
      simp only [List.get, Fin.isValue]
      all_goals
        exact withBotDegree_le_of_repr_le <| by decide +kernel
    }
  · simp -- here the remainder is 0, whose support set is empty, so `simp` solves it...

#print axioms example7

lemma example8 :
    lex.IsRemainder (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4 + X 3 ^ 5: MvPolynomial (Fin 6) ℚ)
      {X 3, X 4 + X 5} (X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 4) := by
  -- convert set to `Set.image list.get`
  simp only [← Set.range_get_nil, ← Set.range_get_singleton, ← Set.range_get_cons_list]
  -- use index
  rw [IsRemainder.isRemainder_range_fintype, ← exists_and_right]
  use [X 3 ^ 4, 0].get
  split_ands
  · simp [Fin.univ_succ, -List.get_eq_getElem, List.get] -- convert sum to add
    try grind-- PIT, we will rely on reflection
  · intro i
    fin_cases i
    all_goals {
      -- simp? [-List.get_eq_getElem, List.get, -degree_mul', -map_add]
      simp only [List.get, Fin.isValue]
      all_goals {
        exact withBotDegree_le_of_repr_le <| by decide +kernel
      }
    }
  · -- simp_rw [MvPolynomial.SortedRepr.support_eq]
    rw [Function.Surjective.forall (AddEquiv.surjective (SortedFinsupp.lexAddEquiv compare))]
    simp only [MvPolynomial.SortedRepr.support_eq, Finset.mem_map_equiv,
      Fin.isValue, List.length_nil, List.length_cons,
      EquivLike.coe_symm_apply_apply, List.mem_toFinset]
    intro x h i
    fin_cases i
    all_goals
      simp only [List.get]
      rw [← tsub_eq_zero_iff_le, MvPolynomial.SortedRepr.lex_degree_eq]
      convert_to _ → ¬ SortedFinsupp.toFinsupp _ - SortedFinsupp.toFinsupp x = 0
      rw [← SortedFinsupp.toFinsupp_tsub, SortedFinsupp.toFinsupp_eq_zero_iff]
      decide +kernel +revert

#print axioms example8
