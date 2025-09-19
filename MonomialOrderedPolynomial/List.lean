import Mathlib

/-!
# Definition of `List.mergeWith`

This file defines `mergeWith`, merging two strictly sorted `List`s into a new strictly sorted
`List`, and prove some theorems describing this behaviour.

## Definitions

- `List.mergeWith l₁ l₂ cmp mergeFn`: merge strictly sorted `l₁ l₂ : List` into a new strictly
  sorted `List`, and elements contained in both `l₁` and `l₂` but equal w.r.t. `cmp` will be merged
  with `mergeFn`, which may return a new value, or return `none`, so that there will be no
  element for them in the new `List`.
- `List.mergeWithByFuel l₁ l₂ cmp mergeFn (fuel := 2 ^ 62)`: do the same thing as mergeWith, but
  prove termination with fuel so that it can be reduced well in the kernel.

## Theorems

- `mergeWithByFuel_eq`: the equivalence between `mergeWith` and `mergeWithByFuel`
- `mergeWith_pairwise_of_pairwise`, `mergeWith_sorted_of_sorted`, `mem_mergeWith_iff`,
  `mem_mergeWith_iff'`: the correctness of `mergeWith`.

## Implementation notes

An argument `cmp : α → α → Ordering` instead of instance `LinearOrder` or `Ord` is used to pass the
order to compare elements, since

1. (with `LinearOrder` and `Ord`) it would be inconvenient to use a different order on the same type;
2. the order used here isn't required to be antisymmetric, and ensuring elements in the list are strictly
  sorted is enough;

-/

namespace List

section

variable {α : Type*} (l l₁ l₂ : List α) (cmp : α → α → Ordering)
  (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)

/--
merge strictly sorted `l₁ l₂ : List` into a new strictly sorted
`List`, and elements contained in both `l₁` and `l₂` but equal w.r.t. `cmp` will be merged with
`mergeFn`, which may return a new value, or return `none` so that there will be no
element for them in the new `List`.
  -/
def mergeWith (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α) : List α :=
  match l₁, l₂ with
  | _, [] => l₁
  | [], _ => l₂
  | h₁ :: l₁', h₂ :: l₂' =>
    match h : cmp h₁ h₂ with
    | .lt => h₁ :: mergeWith l₁' (.cons h₂ l₂') cmp mergeFn
    | .gt => h₂ :: mergeWith (.cons h₁ l₁') l₂' cmp mergeFn
    | .eq =>
      match mergeFn h₁ h₂ h with
      | none => mergeWith l₁' l₂' cmp mergeFn
      | some a => a :: mergeWith l₁' l₂' cmp mergeFn
termination_by l₁.length + l₂.length
decreasing_by
  · simp
  · simp
  · simp
    linarith

@[simp]
lemma mergeWith_left_nil : mergeWith [] l cmp mergeFn = l := by
  unfold mergeWith
  split; rfl; rfl; simp at *

@[simp]
lemma mergeWith_right_nil : mergeWith l [] cmp mergeFn = l := by
  unfold mergeWith
  split; rfl; rfl; simp at *

/--
Do the same thing as mergeWith, but prove termination with a natural number fuel so that it can be
reduced well in the kernel.
-/
-- for reduction in kernel
def mergeWithByFuel (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α) (fuel := 2 ^ 62) : List α :=
  match fuel with
  | 0 => match l₁, l₂ with
    | [], l₁ => l₁
    | l₁, [] => l₁
    | l₁, l₂ =>
      -- it is actually unreachable with default fuel
      mergeWith l₁ l₂ cmp mergeFn
  | .succ fuel =>
    match l₁, l₂ with
    | _, [] => l₁
    | [], _ => l₂
    | h₁ :: l₁', h₂ :: l₂' =>
      match h : cmp h₁ h₂ with
      | .lt => h₁ :: mergeWithByFuel l₁' l₂ cmp mergeFn fuel
      | .gt => h₂ :: mergeWithByFuel l₁ l₂' cmp mergeFn fuel
      | .eq =>
        match mergeFn h₁ h₂ h with
        | none => mergeWithByFuel l₁' l₂' cmp mergeFn fuel
        | some a => a :: mergeWithByFuel l₁' l₂' cmp mergeFn fuel

lemma mergeWithByFuel_eq {fuel : Nat}
    (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α) :
    mergeWithByFuel l₁ l₂ cmp mergeFn fuel = mergeWith l₁ l₂ cmp mergeFn := by
  unfold mergeWithByFuel
  split
  · split <;> simp
  · rw [mergeWith.eq_def l₁ l₂ cmp mergeFn]
    rcases h₁ : l₁ <;> rcases h₂ : l₂
    · simp
    · simp
    · simp
    · expose_names
      simp
      rw [mergeWithByFuel_eq, mergeWithByFuel_eq, mergeWithByFuel_eq]

lemma mergeWithByFuel_eq' (fuel : Nat := 2 ^ 62) : @mergeWithByFuel (fuel := fuel) = @mergeWith := by
  funext
  simp [mergeWithByFuel_eq]

-- lemma mergeWith_symm (l₁ l₂ : List α) (cmp : α → α → Ordering)
--     (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
--     [Std.OrientedCmp cmp] [IsSymmOp mergeFn] :
--     mergeWith l₁ l₂ cmp mergeFn = mergeWith l₂ l₁ cmp mergeFn := by
--   cases' l₁ with _ l₁'
--   · simp
--   cases' l₂ with _ l₂'
--   · simp
--   simp [mergeWith]
--   rw [mergeWith_symm l₁' (_ :: _), mergeWith_symm l₂' (_ :: _),
--     Std.OrientedCmp.eq_swap (cmp := cmp)]
--   split
--   · expose_names
--     simp at heq
--     simp [heq]
--   · expose_names
--     simp at heq
--     simp [heq]
--   · expose_names
--     simp at heq
--     simp [heq]
--     rw [mergeWith_symm l₁', IsSymmOp.symm_op (op := mergeFn)]
-- termination_by l₁.length + l₂.length

instance [Std.TransCmp cmp] : IsTrans _ (cmp · · = .lt) where
  trans := fun _ _ _ => Std.TransCmp.lt_trans

instance [Std.TransCmp cmp] : IsTrans _ (cmp · · = .gt) where
  trans := fun _ _ _ => Std.TransCmp.gt_trans

lemma exists_mem_mergeWith_cmp_eq {a} {l₁ l₂ : List α} {cmp : α → α → Ordering}
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    (h : a ∈ mergeWith l₁ l₂ cmp mergeFn) :
    a ∈ l₁ ∨ a ∈ l₂ ∨
      ∃ a₁ ∈ l₁, ∃ a₂ ∈ l₂, ∃ (h : cmp a₁ a₂ = .eq), a = mergeFn a₁ a₂ h := by
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
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    [Fact <| ∀ a b : α, (h : cmp a b = Ordering.eq) → ∀ a' ∈ mergeFn a b h, cmp a a' = .eq]
    (h : a ∈ mergeWith l₁ l₂ cmp mergeFn) :
    (∃ a' ∈ l₁, cmp a a' = .eq) ∨ ∃ a' ∈ l₂, cmp a a' = .eq := by
  obtain h | h | ⟨a₁, h₁, a₂, h₂, h, h'⟩ := exists_mem_mergeWith_cmp_eq mergeFn h
  · left
    exact ⟨a, h, Std.ReflCmp.compare_self⟩
  · right
    exact ⟨a, h, Std.ReflCmp.compare_self⟩
  · expose_names
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
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    [Fact <| ∀ a b : α, (h : cmp a b = Ordering.eq) → ∀ a' ∈ mergeFn a b h, cmp a a' = .eq] :
    mergeWith l₁ l₂ cmp mergeFn |>.Pairwise (cmp · · = .lt) := by
  expose_names
  have hfn := inst_1.elim
  unfold mergeWith
  split
  · exact h₁
  · exact h₂
  split
  · expose_names
    rw [← List.chain'_iff_pairwise, chain'_cons', List.chain'_iff_pairwise]
    split_ands
    · intro y hy
      apply mem_of_mem_head? at hy
      apply exists_mem_mergeWith_cmp_eq' at hy
      simp [Std.OrientedCmp.eq_comm (a:=y)] at hy
      rcases hy with ⟨a₁, hy⟩ | hy | ⟨a₂, hy⟩
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        exact (pairwise_cons.mp h₁).1 _ hy.1
      · exact Std.TransCmp.lt_of_lt_of_eq heq hy
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        apply Std.TransCmp.lt_trans heq
        exact (pairwise_cons.mp h₂).1 _ hy.1
    · rw [pairwise_cons] at h₁
      exact mergeWith_pairwise_of_pairwise h₁.2 h₂ ..
  · expose_names
    rw [← List.chain'_iff_pairwise, chain'_cons', List.chain'_iff_pairwise]
    split_ands
    · intro y hy
      apply mem_of_mem_head? at hy
      apply exists_mem_mergeWith_cmp_eq' at hy
      simp [Std.OrientedCmp.eq_comm (a:=y)] at hy
      rw [Std.OrientedCmp.gt_iff_lt] at heq
      rcases hy with (hy | ⟨a₁, hy⟩) | ⟨a₂, hy⟩
      · exact Std.TransCmp.lt_of_lt_of_eq heq hy
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        apply Std.TransCmp.lt_trans heq
        exact (pairwise_cons.mp h₁).1 _ hy.1
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        exact (pairwise_cons.mp h₂).1 _ hy.1
    · rw [pairwise_cons] at h₂
      exact mergeWith_pairwise_of_pairwise h₁ h₂.2 ..
  · rw [pairwise_cons] at h₁ h₂
    have := mergeWith_pairwise_of_pairwise h₁.2 h₂.2 mergeFn
    split
    · exact this
    · rw [← List.chain'_iff_pairwise, List.chain'_cons', List.chain'_iff_pairwise]
      refine ⟨?_, this⟩
      intro y hy
      apply mem_of_mem_head? at hy
      apply exists_mem_mergeWith_cmp_eq' at hy
      expose_names
      specialize hfn h₁_1 h₂_1 heq a heq_1
      simp [Std.OrientedCmp.eq_comm (a := y)] at hy
      rcases hy with ⟨a₁, hy⟩ | ⟨a₂, hy⟩
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        rw [Std.OrientedCmp.eq_comm] at hfn
        apply Std.TransCmp.lt_of_eq_of_lt hfn
        exact h₁.1 _ hy.1
      · refine Std.TransCmp.lt_of_lt_of_eq ?_ hy.2
        rw [Std.OrientedCmp.eq_comm] at hfn
        apply Std.TransCmp.lt_of_eq_of_lt hfn
        apply Std.TransCmp.lt_of_eq_of_lt heq
        exact h₂.1 _ hy.1
termination_by l₁.length + l₂.length

lemma mergeWith_sorted_of_sorted {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Sorted (cmp · · = .lt)) (h₂ : l₂.Sorted (cmp · · = .lt))
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    [Fact <| ∀ a b : α, (h : cmp a b = Ordering.eq) → ∀ a' ∈ mergeFn a b h , cmp a a' = .eq] :
    mergeWith l₁ l₂ cmp mergeFn |>.Sorted (cmp · · = .lt) :=
  mergeWith_pairwise_of_pairwise h₁ h₂ mergeFn

theorem Pairwise.eq_or_rel_of_mem {α} {l : List α} {R : α → α → Prop} (h : l.Pairwise R) {a b : α} (h1 : a ∈ l)
    (h2 : b ∈ l) : a = b ∨ R a b ∨ R b a := by
  match l with
  | [] => simp at h1
  | x :: l' =>
    simp at h1 h2 h
    rcases h1 with h1eq | h1mem <;> rcases h2 with h2eq | h2mem
    · simp [h1eq, h2eq]
    · simp [h1eq ▸ h.1 b h2mem]
    · simp [h2eq ▸ h.1 a h1mem]
    · exact Pairwise.eq_or_rel_of_mem h.2 h1mem h2mem

theorem _root_.iff_of_imp_of_imp_of_imp_iff {p q r : Prop} (hp : p → r) (hq : q → r) (h : r → (p ↔ q)) : p ↔ q :=
  ⟨fun p' ↦ h (hp p') |>.mp p', fun q' ↦ h (hq q') |>.mpr q'⟩

lemma mem_mergeWith_iff {a : α} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Pairwise (cmp · · = .lt)) (h₂ : l₂.Pairwise (cmp · · = .lt))
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    [Fact <| ∀ a b : α, (h : cmp a b = Ordering.eq) → ∀ a' ∈ mergeFn a b h, cmp a a' = .eq] :
    a ∈ mergeWith l₁ l₂ cmp mergeFn ↔
      if ∃ x₁ ∈ l₁, cmp a x₁ = .eq then
        ∀ x₁ ∈ l₁, (h1 : cmp a x₁ = .eq) →
          if ∃ x₂ ∈ l₂, cmp a x₂ = .eq then
            ∀ x₂ ∈ l₂, (h2 : cmp a x₂ = .eq) →
              a = mergeFn x₁ x₂ (Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm h1) h2)
          else
            a = x₁
      else
        (∃ x₂ ∈ l₂, cmp a x₂ = .eq) ∧ ∀ x₂ ∈ l₂, cmp a x₂ = .eq → a = x₂
    := by
  match l₁, l₂ with
  | nil, nil => simp
  | nil, l₂ =>
    simp
    constructor
    · intro h
      refine ⟨⟨a, ?_⟩, ?_⟩
      · simp [h, Std.ReflCmp.cmp_eq_of_eq rfl]
      · intro a' h' haa'
        apply (Pairwise.eq_or_rel_of_mem · h h') at h₂
        rcases h₂ with h₂ | h₂ | h₂
        · exact h₂
        · simp [h₂] at haa'
        · simp [Std.OrientedCmp.gt_of_lt h₂] at haa'
    · intro ⟨⟨a', ha', haa'⟩, h''⟩
      exact h'' a' ha' haa' ▸ ha'
  | l₁, nil =>
    simp
    constructor
    · intro h
      refine ⟨⟨a, ?_⟩, ?_⟩
      · simp [h, Std.ReflCmp.cmp_eq_of_eq rfl]
      · intro a' h' haa'
        apply (Pairwise.eq_or_rel_of_mem · h h') at h₁
        rcases h₁ with h₁ | h₁ | h₁
        · exact h₁
        · simp [h₁] at haa'
        · simp [Std.OrientedCmp.gt_of_lt h₁] at haa'
    · intro ⟨⟨a', ha', haa'⟩, h''⟩
      exact h'' a' ha' haa' ▸ ha'
  | a₁ :: l₁', a₂ :: l₂' =>
    unfold mergeWith
    split
    · by_cases h : a = a₁
      · expose_names
        simp at h₁ h₂
        have : ¬ ∃ a ∈ l₂', cmp a₁ a = Ordering.eq := by
          push_neg
          intro a' ha'
          simp [Std.TransCmp.lt_trans heq <| h₂.1 a' ha']
        simp [*, Std.ReflCmp.compare_self]
        intro a' ha' haa'
        simp [h₁.1 a' ha'] at haa'
      · expose_names
        apply iff_of_imp_of_imp_of_imp_iff (r := cmp a a₁ ≠ .eq)
        · intro ha
          simp at h₁ h₂
          simp [h] at ha
          apply exists_mem_mergeWith_cmp_eq' at ha
          simp at ha
          rcases ha with ⟨a', ha', haa'⟩ | haa₁ | ⟨a', ha', haa'⟩
          · simp [Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₁.1 a' ha']
          · simp [Std.TransCmp.gt_of_eq_of_gt haa₁ <| Std.OrientedCmp.gt_of_lt heq]
          · have := Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₂.1 a' ha'
            simp [Std.TransCmp.gt_of_gt_of_gt this <| Std.OrientedCmp.gt_of_lt heq]
        · intro h'
          by_contra haa₁
          simp [*, Std.TransCmp.lt_of_eq_of_lt haa₁ heq] at h'
          obtain ⟨a', ha', haa'⟩ := h'.1.1
          simp at h₂
          have := Std.OrientedCmp.gt_of_lt <| Std.TransCmp.lt_trans heq <| h₂.1 a' ha'
          simp [Std.TransCmp.gt_of_eq_of_gt haa' this] at haa₁
        · simp at h₁
          intro r
          simp [mem_mergeWith_iff h₁.2 h₂, *]
    · expose_names
      apply Std.OrientedCmp.lt_of_gt at heq
      by_cases h : a = a₂
      · simp at h₁ h₂
        have : ¬ ∃ a ∈ l₁', cmp a₂ a = Ordering.eq := by
          push_neg
          intro a' ha'
          simp [Std.TransCmp.lt_trans heq <| h₁.1 a' ha']
        simp [*, Std.ReflCmp.compare_self]
        intro a' ha' haa'
        simp [h₂.1 a' ha'] at haa'
      · apply iff_of_imp_of_imp_of_imp_iff (r := cmp a a₂ ≠ .eq)
        · intro ha
          simp at h₁ h₂
          simp [h] at ha
          apply exists_mem_mergeWith_cmp_eq' at ha
          simp at ha
          rcases ha with (haa₁ | ⟨a', ha', haa'⟩) | ⟨a', ha', haa'⟩
          · simp [Std.TransCmp.gt_of_eq_of_gt haa₁ <| Std.OrientedCmp.gt_of_lt heq]
          · have := Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₁.1 a' ha'
            simp [Std.TransCmp.gt_of_gt_of_gt this <| Std.OrientedCmp.gt_of_lt heq]
          · simp [Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₂.1 a' ha']
        · intro h'
          by_contra haa₂
          simp [*, Std.TransCmp.lt_of_eq_of_lt haa₂ heq] at h'
          obtain ⟨a', ha', haa'⟩ := h'.1
          simp at h₁
          have := Std.OrientedCmp.gt_of_lt <| Std.TransCmp.lt_trans heq <| h₁.1 a' ha'
          simp [Std.TransCmp.gt_of_eq_of_gt haa' this] at haa₂
        · simp at h₂
          intro r
          simp [mem_mergeWith_iff h₁ h₂.2, *]
    · expose_names
      simp at h₁ h₂
      by_cases h : cmp a a₁ = .eq
      · simp [h, Std.TransCmp.eq_trans h heq]
        have ha : ¬ a ∈ l₁'.mergeWith l₂' cmp mergeFn := by
          by_contra ha
          rcases exists_mem_mergeWith_cmp_eq' _ ha with ⟨a', ha', haa'⟩ | ⟨a', ha', haa'⟩
          · simp [Std.TransCmp.lt_of_eq_of_lt h <| h₁.1 a' ha'] at haa'
          · simp [Std.TransCmp.lt_of_eq_of_lt (Std.TransCmp.eq_trans h heq) <| h₂.1 a' ha'] at haa'
        split
        · expose_names
          simp [heq_1, ha]
        · expose_names
          simp [heq_1, ha]
          apply iff_of_imp_of_imp_of_imp_iff (r := a_1 = a) eq_comm.mp
          · simp
            exact fun p _ _ ↦ p.symm
          · intro this
            simp [this] at *
            split_ands
            · intro a' ha' haa'
              apply Std.TransCmp.eq_trans <| Std.OrientedCmp.eq_symm <| Std.TransCmp.eq_trans h heq
                at haa'
              simp [h₂.1 a' ha'] at haa'
            · intro a' ha' haa'
              apply Std.TransCmp.eq_trans <| Std.OrientedCmp.eq_symm h at haa'
              simp [h₁.1 a' ha'] at haa'
      · simp
        have ha {a_1} (ha_1 : mergeFn a₁ a₂ heq = some a_1) : a ≠ a_1 := by
          by_contra! ha
          rw [ha.symm] at ha_1
          simp at inst_1
          apply inst_1.elim _ _ heq _ at ha_1
          exact h <| Std.OrientedCmp.eq_symm ha_1
        apply iff_of_imp_of_imp_of_imp_iff (r := cmp a a₁ = .gt)
        · suffices a ∈ l₁'.mergeWith l₂' cmp mergeFn → cmp a a₁ = Ordering.gt by aesop
          intro h'
          apply Std.OrientedCmp.gt_of_lt
          apply exists_mem_mergeWith_cmp_eq' at h'
          rcases h' with ⟨a', ha', haa'⟩ | ⟨a', ha', haa'⟩
          · exact Std.TransCmp.lt_of_lt_of_eq (h₁.1 a' ha') <| Std.OrientedCmp.eq_symm haa'
          · exact Std.TransCmp.lt_of_lt_of_eq (Std.TransCmp.lt_of_eq_of_lt heq <| h₂.1 a' ha')
              <| Std.OrientedCmp.eq_symm haa'
        · have h2 : ¬cmp a a₂ = Ordering.eq := by
            contrapose! h
            exact Std.TransCmp.eq_trans h <| Std.OrientedCmp.eq_comm.mp heq
          simp [*]
          by_cases ha : ∃ a_1 ∈ l₁', cmp a a_1 = Ordering.eq
          · rintro -
            obtain ⟨a', ha', haa'⟩ := ha
            exact Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₁.1 a' ha'
          · simp [ha, -forall_exists_index]
            rintro ⟨a', ha', haa'⟩ -
            refine Std.TransCmp.gt_of_gt_of_eq ?_ (Std.OrientedCmp.eq_symm heq)
            exact Std.TransCmp.gt_of_eq_of_gt haa' <| Std.OrientedCmp.gt_of_lt <| h₂.1 a' ha'
        intro h'
        simp [h', Std.TransCmp.gt_of_gt_of_eq h' heq]
        split
        · simp [mem_mergeWith_iff h₁.2 h₂.2]
        · expose_names
          simp [ha heq_1, mem_mergeWith_iff h₁.2 h₂.2]

lemma _root_.Transitive.ofTransCmp (cmp : α → α → Ordering) [Std.TransCmp cmp] :
    Transitive (cmp · · = .eq) := fun _ _ _ => Std.TransCmp.eq_trans

lemma _root_.Equivalence.ofTransCmp (cmp : α → α → Ordering) [Std.TransCmp cmp] :
    Equivalence (cmp · · = .eq) where
  refl := fun _ ↦ Std.ReflCmp.compare_self
  symm := Std.OrientedCmp.eq_symm
  trans := Std.TransCmp.eq_trans

lemma not_exists_and {α : Sort*} {q p : α → Prop} :
    (¬∃ x, q x ∧ p x) ↔ ∀ (x : α), q x → ¬ p x := by
  simp

lemma find?_right_eq_some_iff_of_pairwise {p : α → α → Prop} {l : List α}
    (h : l.Pairwise (¬ p · ·)) (a b : α) [∀ x : α, Decidable (p a x)]
    (hp : ∀ a₁ ∈ l, ∀ a₂ ∈ l, p a a₁ → p a a₂ → p a₁ a₂) :
    (l.find? (p a ·)) = some b ↔ b ∈ l ∧ p a b := by
  constructor
  · intro h
    exact ⟨mem_of_find?_eq_some h, of_decide_eq_true <| find?_some (p := fun x ↦ decide (p a x)) h⟩
  intro ⟨hb, hab⟩
  match h' : (l.find? (p a ·)) with
  | none =>
    simp at h'
    simp [h' _ hb] at hab
  | some b' =>
      have hb' := mem_of_find?_eq_some h'
      have hab' := of_decide_eq_true (p := p a b') <| find?_some (p := fun x ↦ decide (p a x)) h'
      apply (Pairwise.eq_or_rel_of_mem · hb' hb) at h
      simp [hp _ hb' _ hb hab' hab, hp _ hb _ hb' hab hab'] at h
      simp [h]

lemma find?_right_eq_some_iff_of_pairwise_equivalence {p : α → α → Prop} (hp : Equivalence p)
    {l : List α} (h : l.Pairwise (¬ p · ·)) (a b : α) [∀ x : α, Decidable (p a x)] :
    (l.find? (p a ·)) = some b ↔ b ∈ l ∧ p a b :=
  find?_right_eq_some_iff_of_pairwise h a b (fun _ _ _ _ h h' ↦ hp.trans (hp.symm h) h')

lemma find?_right_eq_some_iff_of_pairwise' {l : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h : l.Pairwise (cmp · · = .lt)) (a b : α) :
    (l.find? (cmp a · = .eq)) = some b ↔ b ∈ l ∧ cmp a b = .eq := by
  apply find?_right_eq_some_iff_of_pairwise_equivalence (p := (cmp · · = .eq))
  · constructor
    · exact fun a ↦ Std.ReflCmp.compare_self (a := a)
    · exact Std.OrientedCmp.eq_symm
    · exact Std.TransCmp.eq_trans
  · exact Pairwise.imp_of_mem (by simp_intro ..) h

lemma find?_left_eq_some_iff_of_pairwise' {l : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h : l.Pairwise (cmp · · = .lt)) (a b : α) :
    (l.find? (cmp · a = .eq)) = some b ↔ b ∈ l ∧ cmp a b = .eq := by
  convert find?_right_eq_some_iff_of_pairwise' h a b using 5
  exact Std.OrientedCmp.eq_comm

lemma mem_mergeWith_iff' {a : α} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Pairwise (cmp · · = .lt)) (h₂ : l₂.Pairwise (cmp · · = .lt))
    (mergeFn : (a : α) → (b : α) → (cmp a b = .eq) → Option α)
    [fact : Fact (∀ a b : α, (h : cmp a b = Ordering.eq) → ∀ a' ∈ mergeFn a b h, cmp a a' = .eq)] :
    a ∈ mergeWith l₁ l₂ cmp mergeFn ↔
      some a = match h1 : l₁.find? (cmp a · = .eq), h2 : l₂.find? (cmp a · = .eq) with
      | some a', none => a'
      | none, some a' => a'
      | some a'₁, some a'₂ =>
        mergeFn a'₁ a'₂ (by
          rw [find?_right_eq_some_iff_of_pairwise' h₁] at h1
          rw [find?_right_eq_some_iff_of_pairwise' h₂] at h2
          exact Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm h1.2) h2.2
        )
      | none, none => none := by
  rw [mem_mergeWith_iff h₁ h₂ mergeFn]
  apply Pairwise.imp (S := (¬ cmp · · = .eq)) (by simp_intro ..) at h₁
  apply Pairwise.imp (S := (¬ cmp · · = .eq)) (by simp_intro ..) at h₂
  rw [Iff.comm]
  split <;> expose_names
  · simp at heq_1
    rw [find?_right_eq_some_iff_of_pairwise_equivalence (Equivalence.ofTransCmp cmp) h₁] at heq
    simp [not_exists_and.mpr heq_1, show ∃ x₁ ∈ l₁, cmp a x₁ = Ordering.eq from ⟨_, heq⟩]
    constructor
    · simp_intro _ _ h h'
      apply (Pairwise.eq_or_rel_of_mem · heq.1 h) at h₁
      simp [h', Std.OrientedCmp.eq_symm h'] at h₁
      exact h₁
    · intro h
      exact h _ heq.1 heq.2
  · simp at heq
    rw [find?_right_eq_some_iff_of_pairwise_equivalence (Equivalence.ofTransCmp cmp) h₂] at heq_1
    simp [not_exists_and.mpr heq, show ∃ x₂ ∈ l₂, cmp a x₂ = Ordering.eq from ⟨_, heq_1⟩]
    constructor
    · simp_intro _ _ h h'
      apply (Pairwise.eq_or_rel_of_mem · heq_1.1 h) at h₂
      simp [h', Std.OrientedCmp.eq_symm h'] at h₂
      exact h₂
    · intro h
      exact h _ heq_1.1 heq_1.2
  · rw [find?_right_eq_some_iff_of_pairwise_equivalence (Equivalence.ofTransCmp cmp) h₁] at heq
    rw [find?_right_eq_some_iff_of_pairwise_equivalence (Equivalence.ofTransCmp cmp) h₂] at heq_1
    simp [show ∃ x₁ ∈ l₁, cmp a x₁ = Ordering.eq from ⟨_, heq⟩,
      show ∃ x₂ ∈ l₂, cmp a x₂ = Ordering.eq from ⟨_, heq_1⟩]
    constructor
    · simp_intro h x₁ hx₁ hax₁ x₂ hx₂ hax₂
      apply (Pairwise.eq_or_rel_of_mem · heq.1 hx₁) at h₁
      apply (Pairwise.eq_or_rel_of_mem · heq_1.1 hx₂) at h₂
      simp at fact
      apply Fact.elim at fact
      have := Std.TransCmp.eq_trans (Std.OrientedCmp.eq_symm heq.2) heq_1.2
      specialize fact _ _ this _ h.symm
      simp [Std.TransCmp.eq_trans fact hax₁, Std.OrientedCmp.eq_comm] at h₁
      replace this := (Std.TransCmp.congr_left this).symm ▸ Std.TransCmp.eq_trans fact hax₂
      simp [this, Std.OrientedCmp.eq_comm] at h₂
      simp [h₁, h₂]
    · intro h
      exact h _ heq.1 heq.2 _ heq_1.1 heq_1.2
  · simp at heq heq_1
    simp [not_exists_and.mpr heq, not_exists_and.mpr heq_1]

end
