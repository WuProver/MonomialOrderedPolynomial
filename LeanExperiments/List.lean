import Mathlib

-- for `Expanded`
namespace List

section

variable {α : Type*} (l l₁ l₂ : List α) (cmp : α → α → Ordering)
  (mergeFn : α → α → Option α)

def mergeWith (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : α → α → Option α) : List α :=
  match l₁, l₂ with
  | _, [] => l₁
  | [], _ => l₂
  | h₁ :: l₁', h₂ :: l₂' =>
    match cmp h₁ h₂ with
    | .lt => h₁ :: mergeWith l₁' (.cons h₂ l₂') cmp mergeFn
    | .gt => h₂ :: mergeWith (.cons h₁ l₁') l₂' cmp mergeFn
    | .eq =>
      match mergeFn h₁ h₂ with
      | none => mergeWith l₁' l₂' cmp mergeFn
      | some a => a :: mergeWith l₁' l₂' cmp mergeFn
termination_by l₁.length + l₂.length
decreasing_by
  · simp
  · simp
  · simp
    linarith

def mergeWith' : List α :=
  go (l₁.lengthTR + l₂.lengthTR) l₁ l₂
where
  go (fuel : Nat) (l₁ l₂ : List α) :=
  match fuel with
  | 0 => []
  | .succ fuel =>
    match l₁, l₂ with
    | _, [] => l₁
    | [], _ => l₂
    | h₁ :: l₁', h₂ :: l₂' =>
      match cmp h₁ h₂ with
      | .lt => h₁ :: go fuel l₁' l₂
      | .gt => h₂ :: go fuel l₁ l₂'
      | .eq =>
        match mergeFn h₁ h₂ with
        | none => go fuel l₁' l₂'
        | some a => a :: go fuel l₁' l₂'

lemma mergeWith'_go_eq {fuel : Nat}
    (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : α → α → Option α)
    (h : l₁.length + l₂.length <= fuel) :
    mergeWith'.go cmp mergeFn fuel l₁ l₂ = mergeWith l₁ l₂ cmp mergeFn := by
  unfold mergeWith'.go mergeWith
  split
  · simp at h
    simp [h]
  · split
    · rfl
    · rfl
    simp at h
    rw [mergeWith'_go_eq, mergeWith'_go_eq, mergeWith'_go_eq]
    · linarith
    · simp; linarith
    · simp; linarith

lemma mergeWith'_eq : mergeWith' l₁ l₂ cmp mergeFn = mergeWith l₁ l₂ cmp mergeFn := by
  unfold mergeWith'
  simp [← length_eq_lengthTR]
  exact mergeWith'_go_eq _ _ _ _ (le_refl _)

@[simp]
lemma mergeWith_left_nil : mergeWith [] l cmp mergeFn = l := by
  unfold mergeWith
  split; rfl; rfl; simp at *

@[simp]
lemma mergeWith_right_nil : mergeWith l [] cmp mergeFn = l := by
  unfold mergeWith
  split; rfl; rfl; simp at *

lemma mergeWith_symm (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : α → α → Option α)
    [Std.OrientedCmp cmp] [IsSymmOp mergeFn] :
    mergeWith l₁ l₂ cmp mergeFn = mergeWith l₂ l₁ cmp mergeFn := by
  cases' l₁ with _ l₁'
  · simp
  cases' l₂ with _ l₂'
  · simp
  simp [mergeWith]
  rw [mergeWith_symm l₁' (_ :: _), mergeWith_symm l₂' (_ :: _),
    Std.OrientedCmp.eq_swap (cmp := cmp)]
  split
  · expose_names
    simp at heq
    simp [heq]
  · expose_names
    simp at heq
    simp [heq]
  · expose_names
    simp at heq
    simp [heq]
    rw [mergeWith_symm l₁', IsSymmOp.symm_op (op := mergeFn)]
termination_by l₁.length + l₂.length

instance [Std.TransCmp cmp] : IsTrans _ (cmp · · = .lt) where
  trans := fun _ _ _ => Std.TransCmp.lt_trans

instance [Std.TransCmp cmp] : IsTrans _ (cmp · · = .gt) where
  trans := fun _ _ _ => Std.TransCmp.gt_trans

lemma exists_mem_mergeWith_cmp_eq {a} {l₁ l₂ : List α} {cmp : α → α → Ordering}
    (mergeFn : α → α → Option α)
    (h : a ∈ mergeWith l₁ l₂ cmp mergeFn) :
    a ∈ l₁ ∨ a ∈ l₂ ∨
      ∃ a₁ ∈ l₁, ∃ a₂ ∈ l₂, cmp a₁ a₂ = .eq ∧ a = mergeFn a₁ a₂ := by
  -- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Non-structural.20recursivity.2C.20termination_by.20arguments/with/523811369
  match l₁, l₂ with
  | nil, _ => simp at h; simp [h]
  | _, nil => simp at h; simp [h]
  | _ :: l₁', _ :: l₂' =>
    simp [mergeWith] at h
    split at h
    · simp at h
      rcases h with h | h
      · simp [h]
      have := exists_mem_mergeWith_cmp_eq mergeFn h
      rcases this with h' | h' | h'
      · simp [h']
      · simp [h']
      right; right
      simp at h'
      simp [h']
    · simp at h
      rcases h with h | h
      · simp [h]
      have := exists_mem_mergeWith_cmp_eq mergeFn h
      rcases this with h' | h' | ⟨a₁, h₁, a₂, h₂, h'⟩
      · simp [h']
      · simp [h']
      right; right
      refine ⟨a₁, ?_, a₂, ?_, h'⟩
      all_goals simp [h₁, h₂]
    · split at h
      · have := exists_mem_mergeWith_cmp_eq mergeFn h
        rcases this with h' | h' | ⟨a₁, h₁, a₂, h₂, h'⟩
        · simp [h']
        · simp [h']
        right; right
        refine ⟨a₁, ?_, a₂, ?_, h'⟩
        all_goals simp [h₁, h₂]
      · simp at h
        rcases h with h | h
        · expose_names
          right; right
          refine ⟨head, ?_, head_1, ?_, heq, h.symm ▸ heq_1.symm⟩
          all_goals simp
        have := exists_mem_mergeWith_cmp_eq mergeFn h
        rcases this with h' | h' | ⟨a₁, h₁, a₂, h₂, h'⟩
        · simp [h']
        · simp [h']
        right; right
        refine ⟨a₁, ?_, a₂, ?_, h'⟩
        all_goals simp [h₁, h₂]
termination_by l₁.length + l₂.length
decreasing_by
  all_goals
    simp_rw [length_cons]
    linarith

lemma exists_mem_mergeWith_cmp_eq' {a} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (mergeFn : α → α → Option α)
    [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a' ∈ mergeFn a b, cmp a a' = .eq]
    (h : a ∈ mergeWith l₁ l₂ cmp mergeFn) :
    (∃ a' ∈ l₁, cmp a a' = .eq) ∨ ∃ a' ∈ l₂, cmp a a' = .eq := by
  obtain h | h | ⟨a₁, h₁, a₂, h₂, h, h'⟩ := exists_mem_mergeWith_cmp_eq mergeFn h
  · left
    exact ⟨a, h, Std.ReflCmp.compare_self⟩
  · right
    exact ⟨a, h, Std.ReflCmp.compare_self⟩
  ·
    expose_names
    have := inst_1.elim a₁ a₂ h
    simp at this
    specialize this a h'.symm
    right
    refine ⟨a₂, h₂, ?_⟩
    refine Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm this) h


-- lemma mergeWith_head_lt_of_lt {h a₁ a₂} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
--     (h₁ : (a₁ :: l₁).Pairwise (cmp · · = .lt)) (h₂ : (a₂ :: l₂).Pairwise (cmp · · = .lt))
--     (mergeFn : α → α → Option α)
--     [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a', mergeFn a b = some a' → cmp a a' = .eq] :
--     mergeWith l₁ l₂ cmp mergeFn |>.head?.all (cmp h · = .lt) := by
--   expose_names
--   have := inst_1.elim
--   #check Option.mem_def
--   cases l₁
--   simp
--   sorry
--   sorry
-- -- #check mergeTR_ok
--   -- rw [Option.forall_m]
--   -- simp? at h₁' h₂'




lemma mergeWith_pairwise_of_pairwise {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Pairwise (cmp · · = .lt)) (h₂ : l₂.Pairwise (cmp · · = .lt))
    (mergeFn : α → α → Option α)
    [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a' ∈ mergeFn a b, cmp a a' = .eq] :
    mergeWith l₁ l₂ cmp mergeFn |>.Pairwise (cmp · · = .lt) := by
  expose_names
  have hfn:= inst_1.elim
  unfold mergeWith
  split
  · exact h₁
  · exact h₂
  split
  · expose_names
    rw [← List.chain'_iff_pairwise, chain'_cons']
    split_ands
    · intro y hy
      apply mem_of_mem_head? at hy
      apply exists_mem_mergeWith_cmp_eq' at hy
      rcases hy with ⟨a₁, hy⟩ | ⟨a₂, hy⟩
      ·
        sorry
      ·
        sorry
    sorry
    -- -- rw [List.chain_iff]
    -- have := mergeWith_sorted_of_sorted (List.sorted_cons.mp h₁).2 h₂ mergeFn
    -- refine ⟨?_, this⟩
    -- · intro b hb
    --   have := List.rel_of_sorted_cons h₁

    --   sorry

  sorry
  ·
    -- rw [← List.chain'_iff_pairwise, List.chain'_cons', List.chain'_iff_pairwise] at h₁ h₂
    rw [pairwise_cons] at h₁ h₂
    have := mergeWith_pairwise_of_pairwise h₁.2 h₂.2 mergeFn
    split
    · exact this
    · rw [← List.chain'_iff_pairwise, List.chain'_cons', List.chain'_iff_pairwise]
      refine ⟨?_, this⟩
      intro y hy
      expose_names
      specialize hfn h₁_1 h₂_1 heq a heq_1
      -- obtain h := exists_mem_mergeWith_cmp_eq mergeFn
      sorry


      -- exact Std.TransCmp.lt_of_eq_of_lt (Std.TransCmp.eq_trans this) h₁ a
      -- simp at this

lemma mem_mergeWith_iff {a} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Pairwise (cmp · · = .lt)) (h₂ : l₂.Pairwise (cmp · · = .lt))
    (mergeFn : α → α → Option α)
    [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a' ∈ mergeFn a b, cmp a a' = .eq] :
    a ∈ mergeWith l₁ l₂ cmp mergeFn ↔
    (a ∈ l₁ ↔ ¬ a ∈ l₂) ∨
      ∃ a₁ ∈ l₁, ∃ a₂ ∈ l₂, cmp a₁ a₂ = .eq ∧ a = mergeFn a₁ a₂
  := sorry

  -- sorry

end

#reduce [1, 2, 4, 5].mergeWith' [1, 3, 9] cmp fun _ _ => none


end List
