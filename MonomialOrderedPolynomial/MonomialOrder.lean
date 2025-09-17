import Mathlib.Data.Finsupp.MonomialOrder
import MonomialOrderedPolynomial.SortedFinsupp
import MonomialOrderedPolynomial.Ordering

-- todo: generalize
namespace SortedFinsupp

variable {σ} {R} [Zero R] (cmp : σ → σ → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
variable [Ord R] [Std.TransOrd R] [Std.LawfulEqOrd R]
variable [fact : Fact <| ∀ y : R, y ≠ 0 → compare 0 y = .lt]

def lex : List ((_ : σ) × R) → List ((_ : σ) × R) → Ordering
  | .nil, .nil => .eq
  | .nil, .cons ..  => .lt
  | .cons .., .nil => .gt
  | .cons pw₁ m₁, .cons pw₂ m₂ =>
    cmp pw₂.1 pw₁.1 |>.then <|
      compare pw₁.2 pw₂.2 |>.then <|
        lex m₁ m₂

instance : Ord (Lex <| SortedFinsupp σ R cmp) where
  compare l₁ l₂ := lex cmp l₁.val.val l₂.val.val

-- instance : LE (Lex <| SortedFinsupp σ R cmp) where
--   le l₁ l₂ := compare l₁ l₂ |>.isLE

lemma _root_.Ordering.then_of_ne_eq (o o' : Ordering) (h : o ≠ .eq) : o.then o' = o := by
  simp [Ordering.then]

lemma lex_eq [DecidableEq σ] (l₁ l₂ : SortedFinsupp σ R cmp) :
    compare (toLex l₁) (toLex l₂) = .lt ↔
      Pi.Lex (cmp · · = .lt) (compare · · = .lt) l₁ l₂ := by
  convert_to lex cmp l₁.val.val l₂.val.val = .lt ↔ _
  unfold lex
  split
  · expose_names
    simp [show l₁ = 0 by rwa [DSortedFinsupp.eq_iff, DSortedListMap.eq_iff],
      show l₂ = 0 by rwa [DSortedFinsupp.eq_iff, DSortedListMap.eq_iff], Pi.Lex]
  · expose_names
    simp [show l₁ = 0 by rwa [DSortedFinsupp.eq_iff, DSortedListMap.eq_iff], Pi.Lex,
      eq_comm (a := (0 : R)), DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys l₂,
      DSortedListMap.keys, heq_1]
    use head.1
    split_ands
    · intro j hj
      by_contra! h
      rw [imp_iff_not_or] at h
      rcases h with h | ⟨_, h⟩
      · simp at h
        simp [h, Std.ReflCmp.compare_self] at hj
      · have := heq_1 ▸ l₂.val.pairwise
        simp [← Std.OrientedCmp.gt_iff_lt] at this
        simp [this.1 _ h] at hj
    · apply fact.elim _
      rw [ne_eq, DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys, heq_1]
      simp
  · expose_names
    simp [show l₂ = 0 by rwa [DSortedFinsupp.eq_iff, DSortedListMap.eq_iff], Pi.Lex,
      DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys l₁, DSortedListMap.keys, heq]
    intro x' h
    rw [← Std.OrientedCmp.gt_iff_lt]
    by_cases h' : l₁ x' = 0
    · simp [Std.ReflCmp.cmp_eq_of_eq h'.symm]
    · simp [fact.elim _ h']
  · expose_names
    by_cases h : cmp pw₂.fst pw₁.fst = .eq
    · simp [Std.LawfulEqCmp.compare_eq_iff_eq.mp h, Std.ReflCmp.compare_self]
      · by_cases h' : compare pw₁.snd pw₂.snd = .eq
        · simp [Std.LawfulEqCmp.compare_eq_iff_eq.mp h', Std.ReflCmp.compare_self]
          -- should be generalized to DSortedFinsupp.induction later
          let l₁' : SortedFinsupp σ R cmp :=
            ⟨⟨m₁, by simp [List.chain'_cons'.mp (heq ▸ l₁.val.2)]⟩, by have := heq ▸ l₁.2; aesop⟩
          let l₂' : SortedFinsupp σ R cmp :=
            ⟨⟨m₂, by simp [List.chain'_cons'.mp (heq_1 ▸ l₂.val.2)]⟩, by have := heq_1 ▸ l₂.2; aesop⟩
          -- shuold be a theorem
          convert_to compare (toLex l₁') (toLex l₂') = .lt ↔ _
          rw [lex_eq]
          simp [Pi.Lex]
          have hl₁' {j} : l₁ j = if j = pw₁.1 then pw₁.2 else l₁' j := by
            rw [DSortedFinsupp.cons_apply₁ (h := (show m₁ = l₁'.val.val from rfl) ▸ heq)]
            simp
          simp at heq heq_1
          have hl₂' {j} : l₂ j = if j = pw₁.1 then pw₁.2 else l₂' j := by
            rw [DSortedFinsupp.cons_apply₁ (h := (show m₂ = l₂'.val.val from rfl) ▸ heq_1)]
            simp
            simp [Std.LawfulEqCmp.compare_eq_iff_eq.mp h, Std.LawfulEqCmp.compare_eq_iff_eq.mp h']
          have hl₁'2 : l₁' pw₁.1 = 0 := by
            rw [DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys]
            simp
            intro _ h'
            have := List.pairwise_cons.mp ((show m₁ = l₁'.val.val from rfl) ▸ heq ▸ l₁.1.pairwise)
            have := this.1 _ h'
            simp [Std.ReflCmp.compare_self] at this
          have hl₂'2 : l₂' pw₁.1 = 0 := by
            rw [DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys]
            simp
            intro _ h'
            have := List.pairwise_cons.mp ((show m₂ = l₂'.val.val from rfl) ▸ heq_1 ▸l₂.1.pairwise)
            have := this.1 _ h'
            simp [Std.ReflCmp.compare_self, Std.LawfulEqCmp.compare_eq_iff_eq.mp h] at this
          simp [hl₁', hl₂']
          constructor
          · intro ⟨i, hi⟩
            use i
            split_ands
            · intro j hj
              simp [hi.1 _ hj]
            · split_ifs with h''
              · simp [h'', hl₁'2, hl₂'2] at *
              · simp [*]
          · intro ⟨i, hi⟩
            use i
            split_ands
            · intro j hj
              have := hi.1 _ hj
              split_ifs at this
              · simp [*]
              · exact this
            · suffices i ≠ pw₁.fst by
                  simp [this] at hi
                  exact hi.2
              intro h
              simp [h] at hi
        · simp [Pi.Lex, Ordering.then_of_ne_eq (h := h')]
          have hl₁' {j} (hj : cmp j pw₁.1 = .lt) : l₁ j = 0 := by
            apply DSortedFinsupp.cons_apply_eq_zero_of_lt₁ (a' := pw₁.1)
            · simp [heq]
            · exact hj
          have hl₂' {j} (hj : cmp j pw₁.1 = .lt) : l₂ j = 0 := by
            apply DSortedFinsupp.cons_apply_eq_zero_of_lt₁ (a' := pw₂.1)
            · simp [heq_1]
            · exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp h) ▸ hj
          have hl₁'2 : l₁ pw₁.1 = pw₁.2 := by
            convert DSortedFinsupp.cons_apply_eq₁ pw₁ l₁ ..
            simp [heq]
          have hl₂'2 : l₂ pw₁.1 = pw₂.2 := by
            rw [← Std.LawfulEqCmp.compare_eq_iff_eq.mp h]
            convert DSortedFinsupp.cons_apply_eq₁ pw₂ l₂ ..
            · simp [heq_1]
          constructor
          · intro h'
            use pw₁.1
            split_ands
            · intro j hj
              convert_to (0 : R) = 0
              · exact hl₁' hj
              · exact hl₂' hj
              · rfl
            · convert h'
          · intro ⟨i, hi⟩
            rw [← hl₁'2, ← hl₂'2]
            convert hi.2
            all_goals
              rcases h'' : cmp i pw₁.1 with h'' | h'' | h''
              · simp [hl₁' h'', hl₂' h''] at hi
              · exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp h'').symm
              · rw [Std.OrientedCmp.gt_iff_lt] at h''
                have := hi.1 _ h''
                simp [hl₁'2, hl₂'2] at this
                simp [this] at h'
    · simp [Pi.Lex, Ordering.then_of_ne_eq (h := h)]
      constructor
      · intro h
        use pw₂.1
        split_ands
        · intro i h'
          simp [l₂.cons_apply_eq_zero_of_lt₁ (by simp [heq_1]) h',
            l₁.cons_apply_eq_zero_of_lt₁ (by simp [heq]) (Std.TransCmp.lt_trans h' h)]
        · convert fact.elim _ _
          · apply l₁.cons_apply_eq_zero_of_lt₁
            · simp [heq]
              rfl
            · exact h
          · simp [l₂.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys, heq_1]
      · intro ⟨i, hi⟩
        by_contra! h'
        simp [Ordering.ne_lt_iff_isGE, Ordering.isGE_iff_eq_gt_or_eq_eq, h,
          Std.OrientedCmp.gt_iff_lt] at h'
        have : cmp i pw₁.1 |>.isLE := by
          obtain hi := hi.1
          contrapose! hi
          use pw₁.fst
          simp [Std.OrientedCmp.gt_iff_lt] at hi
          refine ⟨hi, ?_⟩
          convert_to pw₁.2 ≠ 0
          · apply l₁.cons_apply_eq₁
            simp [heq]
          · apply l₂.cons_apply_eq_zero_of_lt₁ (a' := pw₂.1)
            · simp [heq_1]
            · exact h'
          · have := l₁.2
            simp [heq] at this
            exact this.1
        obtain hi := hi.2
        revert hi
        simp
        convert_to ¬ compare (l₁ i) 0 =.lt using 3
        · apply l₂.cons_apply_eq_zero_of_lt₁ (a' := pw₂.1)
          · simp [heq_1]
          · exact Std.TransCmp.lt_of_isLE_of_lt this h'
        · by_cases hl₁ : l₁ i = 0
          · simp [hl₁]
          · simp [fact.elim _ hl₁, ← Std.OrientedCmp.gt_iff_lt]
termination_by l₁.val.val.length + l₂.val.val.length
decreasing_by
  simp [*]
  linarith

lemma lex_eq' [DecidableEq σ] (l₁ l₂ : Lex <| SortedFinsupp σ R cmp) :
    compare l₁ l₂ = .lt ↔
      Pi.Lex (cmp · · = .lt) (compare · · = .lt)
      (ofLex l₁ : SortedFinsupp σ R cmp) (ofLex l₂ : SortedFinsupp σ R cmp) :=
  lex_eq ..

instance : Std.OrientedOrd (Lex (SortedFinsupp σ R cmp)) where
  eq_swap {_ _} := eq_swap' ..
where
  eq_swap' (l₁ l₂ : List ((_ : σ) × R)) :
      lex cmp l₁ l₂ = (lex cmp l₂ l₁).swap := by
    unfold lex
    split
    · simp [*]
    · simp [*]
    · simp [*]
    · simp [*, Ordering.swap_then]
      congr
      · exact Std.OrientedCmp.eq_swap
      · exact Std.OrientedCmp.eq_swap
      · exact eq_swap' ..

instance : Std.LawfulEqOrd (Lex (SortedFinsupp σ R cmp)) where
  eq_of_compare {_ _} := by
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact eq_of_compare' _ _
where
  eq_of_compare' (l₁ l₂ : List ((_ : σ) × R)) (h : lex cmp l₁ l₂ = .eq) : l₁ = l₂ := by
    unfold lex at h
    split at h
    · simp
    · simp at h
    · simp at h
    · simp
      simp at h
      have := eq_of_compare' _ _ h.2.2
      aesop

instance instLinearOrder [DecidableEq σ] {R : Type*} [Zero R] [LinearOrder R]
    [fact : Fact <| ∀ y : R, y ≠ 0 → compare 0 y = .lt] :
    LinearOrder (Lex (SortedFinsupp σ R cmp)) where
  compare a b := lex cmp a.1.1 b.1.1
  __ :=
    letI : Ord σ := { compare := cmp }
    letI := (inferInstance : Ord σ).toLE
    letI := (inferInstance : Ord σ).toLT
    letI : Std.LawfulOrd σ := {
      eq_lt_iff_lt := by rfl
      isLE_iff_le := by rfl
    }
    letI : LinearOrder σ := LinearOrder.ofLawfulOrd
    letI : LinearOrder R := inferInstance
    LinearOrder.liftWithOrd'
      (toLex ∘ SortedFinsupp.equivFinsupp ∘ ofLex)
      (β := Lex <| σ →₀ R)
      (by simp [Equiv.injective])
      (by
        intro a b
        rw [eq_comm]
        rcases h : compare a b
        · simp [lex_eq', Pi.Lex, Std.LawfulLTCmp.eq_lt_iff_lt] at h
          simpa [Std.LawfulCmp.eq_lt_iff_lt, Finsupp.lex_lt_iff]
        · simp at h
          simpa [Std.LawfulEqCmp.compare_eq_iff_eq]
        · simp [Std.OrientedCmp.gt_iff_lt, lex_eq', Pi.Lex, Std.LawfulLTCmp.eq_lt_iff_lt] at h
          simpa [Std.OrientedCmp.gt_iff_lt, Std.LawfulCmp.eq_lt_iff_lt, Finsupp.lex_lt_iff]
      )

instance instLinearOrder' {σ} [DecidableEq σ] [LinearOrder σ] {R : Type*} [Zero R] [LinearOrder R]
    [fact : Fact <| ∀ y : R, y ≠ 0 → compare 0 y = .lt] :
    LinearOrder (Lex (SortedFinsupp σ R compare)) where
  compare a b := lex compare a.1.1 b.1.1
  __ :=
    LinearOrder.liftWithOrd'
      (toLex ∘ SortedFinsupp.equivFinsupp ∘ ofLex)
      (β := Lex <| σ →₀ R)
      (by simp [Equiv.injective])
      (by
        intro a b
        rw [eq_comm]
        rcases h : compare a b
        · simp [lex_eq' (cmp := compare), Pi.Lex, Std.LawfulLTCmp.eq_lt_iff_lt] at h
          simpa! [Std.LawfulCmp.eq_lt_iff_lt, Finsupp.lex_lt_iff]
        · simp at h
          simpa [Std.LawfulEqCmp.compare_eq_iff_eq]
        · simp [Std.OrientedCmp.gt_iff_lt, lex_eq' (cmp := compare), Pi.Lex,
            Std.LawfulLTCmp.eq_lt_iff_lt] at h
          simpa [Std.OrientedCmp.gt_iff_lt, Std.LawfulCmp.eq_lt_iff_lt, Finsupp.lex_lt_iff]
      )

def orderIsoFinsupp {σ} [DecidableEq σ] [LinearOrder σ] {R : Type*} [Zero R] [LinearOrder R]
    [fact : Fact <| ∀ y : R, y ≠ 0 → compare 0 y = .lt] :
    OrderIso (Lex (SortedFinsupp σ R compare)) (Lex (Finsupp σ R)) where
  __ := ofLex.trans SortedFinsupp.equivFinsupp |>.trans toLex
  map_rel_iff' := by
    intro a b
    simp [le_iff_lt_or_eq, Finsupp.lex_lt_iff,
      ← Std.LawfulCmp.eq_lt_iff_lt (x := a) (cmp := compare), lex_eq', Pi.Lex]
    simp [Std.LawfulCmp.eq_lt_iff_lt]

instance : Fact <| ∀ y : Nat, y ≠ 0 → compare 0 y = .lt where
  out y := by
    intro h
    simpa [Nat.compare_eq_lt, ← Nat.ne_zero_iff_zero_lt]

instance {R} [AddCommMonoid R] [(a : R) → Decidable (a = 0)] [DecidableEq σ] :
    AddCommMonoid (Lex <| SortedFinsupp σ R cmp) :=
  fast_instance% inferInstanceAs <| AddCommMonoid (SortedFinsupp σ R cmp)

def lexAddEquiv {R} [AddCommMonoid R] [(a : R) → Decidable (a = 0)] [DecidableEq σ] :
    AddEquiv (Lex <| SortedFinsupp σ R cmp) (σ →₀ R) :=
  addEquivFinsupp

instance [DecidableEq σ] {R : Type*} [AddCommMonoid R] [LinearOrder R]
    [Fact <| ∀ y : R, y ≠ 0 → compare 0 y = .lt]
    [inst : Fact <| ∀ (a i j : R), compare i j = compare (a + i) (a + j)] :
    Fact <| ∀ (a i j : Lex <| SortedFinsupp σ R cmp),
      compare i j = compare (a + i) (a + j) where
  out a i j := by
    rcases h : compare i j
    · rw [lex_eq'] at h
      rw [eq_comm, lex_eq']
      simp [Pi.Lex] at *
      obtain ⟨i, hj⟩ := h
      use i
      split_ands
      · intro j' hj'
        simp [hj.1 j' hj']
      · rw [← hj.2, eq_comm]
        exact inst.elim ..
    · rw [eq_comm]
      simp at *
      simp [h]
    · rw [eq_comm]
      simp [Std.OrientedCmp.gt_iff_lt, lex_eq', Pi.Lex] at *
      obtain ⟨i, hj⟩ := h
      use i
      split_ands
      · intro j' hj'
        simp [hj.1 j' hj']
      · rw [← hj.2, eq_comm]
        exact inst.elim ..
