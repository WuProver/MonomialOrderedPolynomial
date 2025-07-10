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

-- for reduction in kernel
def mergeWithByFuel : List α :=
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

lemma mergeWithByFuel_go_eq {fuel : Nat}
    (l₁ l₂ : List α) (cmp : α → α → Ordering)
    (mergeFn : α → α → Option α)
    (h : l₁.length + l₂.length <= fuel) :
    mergeWithByFuel.go cmp mergeFn fuel l₁ l₂ = mergeWith l₁ l₂ cmp mergeFn := by
  unfold mergeWithByFuel.go mergeWith
  split
  · simp at h
    simp [h]
  · split
    · rfl
    · rfl
    simp at h
    rw [mergeWithByFuel_go_eq, mergeWithByFuel_go_eq, mergeWithByFuel_go_eq]
    · linarith
    · simp; linarith
    · simp; linarith

lemma mergeWithByFuel_eq : @mergeWithByFuel = @mergeWith := by
  funext
  unfold mergeWithByFuel
  simp [← length_eq_lengthTR]
  exact mergeWithByFuel_go_eq _ _ _ _ (le_refl _)

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
    (mergeFn : α → α → Option α)
    [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a' ∈ mergeFn a b, cmp a a' = .eq] :
    mergeWith l₁ l₂ cmp mergeFn |>.Sorted (cmp · · = .lt) :=
  mergeWith_pairwise_of_pairwise h₁ h₂ mergeFn

-- open Classical in
lemma mem_mergeWith_iff {a} {l₁ l₂ : List α} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (h₁ : l₁.Pairwise (cmp · · = .lt)) (h₂ : l₂.Pairwise (cmp · · = .lt))
    (mergeFn : α → α → Option α)
    [Fact <| ∀ a b : α, cmp a b = Ordering.eq → ∀ a' ∈ mergeFn a b, cmp a a' = .eq] :
    a ∈ mergeWith l₁ l₂ cmp mergeFn ↔
      some a = match l₁.find? (cmp · a == .eq), l₂.find? (cmp · a == .eq) with
      | some a', none => a'
      | none, some a' => a'
      | some a'₁, some a'₂ => mergeFn a'₁ a'₂
      | _, _ => none := by
  sorry

end

#check Int.mul
#check Int

-- #check List.find
#check Finset.filter_singleton

#loogle List.find?, List.filter

#reduce [1, 2, 4, 5].mergeWithByFuel [1, 3, 9] cmp fun _ _ => none



end List

#check Int.add

structure Int' where
  isNeg : Bool
  abs : Int
-- deriving Decidable

instance inst : BEq Int' where
  beq a b := or (and (a.abs == 0) (b.abs == 0)) (and (a.isNeg == b.isNeg) (a.abs == b.abs))



#print inst

def Int'.mul (a b : Int') : Int' where
  isNeg := xor a.isNeg b.isNeg
  abs := a.abs * b.abs

def Int'.add (a b : Int') : Int' :=
  match xor a.isNeg b.isNeg with
  | true =>
    bif a.abs < b.abs then
      ⟨b.isNeg, b.abs - a.abs⟩
    else
      ⟨a.isNeg, a.abs - b.abs⟩
  | false =>
    ⟨a.isNeg, a.abs + b.abs⟩

def Int'.sub (a b : Int') : Int' :=
  match xor a.isNeg b.isNeg with
  | true =>
    ⟨a.isNeg, a.abs + b.abs⟩
  | false =>
    bif a.abs < b.abs then
      ⟨not a.isNeg, b.abs - a.abs⟩
    else
      ⟨a.isNeg, a.abs - b.abs⟩

def Int.pow' (m : Int) (n : Nat) : Int :=
  match m with
  | .ofNat m => ((m : Nat) ^ n : Nat)
  | .negSucc m => if n % 2 = 0 then
      ((m + 1) ^ n : Nat)
    else - ((m + 1) ^ n : Nat)

def Int'.pow (m : Int') (n : Nat) : Int' :=
  ⟨match m.isNeg with | true => n % 2 != 0 | false => false, m.abs ^ n⟩

def Int'.neg (m : Int') : Int' := ⟨not m.isNeg, m.abs⟩

-- #check or

abbrev test (n : Nat) :=
    let x (m : Nat) : Nat := (min (1 ^ (2 * n) * 2 ^ (2 * n - 1)) (2 ^ (n) * 3 ^ (n - 1)) + 1) ^ m
    (- ((1 : Int) * x 1 - 1)).pow' (2 * n) =
    ((1 : Int) * x 2 - (2 : Int) * x 1 + 1 ).pow' n

abbrev test' (n : Nat) :=
  (List.range (2 * n + 1)).all <|
    fun x =>
      (- ((1 : Int) * x - 1)).pow' (2 * n) = ((1 : Int) * x ^ 2 - (2 : Int) * x + 1 ).pow' n

-- abbrev test' (n : Nat) :=
--     let x (m : Nat) : Nat := (min (1 ^ (2 * n) * 2 ^ (2 * n - 1)) (2 ^ (n) * 3 ^ (n - 1)) + 1) ^ m
--     ((⟨false, 1⟩ : Int') |>.mul ⟨false, x 1⟩ |>.sub ⟨false, 1⟩ |>.neg.pow (2 * n)) =
--     ((⟨false, 1⟩ : Int').mul ⟨false, x 2⟩ |>.sub (⟨false, 2⟩ : Int) x 1 + 1 ).pow' n

abbrev test2 (n : Nat) :=
    let x (m : Nat) : Nat := (max (5 ^ (2 * n) * 2 ^ (2 * n - 1)) (9 ^ (n) * 3 ^ (n - 1)) + 1) ^ m
    (- ((1 : Int) * x 1 - 2)).pow' (2 * n) =
    ((1 : Int) * x 2 - (4 : Int) * x 1 + 4 ).pow' n

abbrev test3 (n : Nat) :=
    let x (m : Nat) : Nat := (min (2 ^ (2 * n) * 2 ^ (2 * n - 1)) (4 ^ (n) * 3 ^ (n - 1)) + 1) ^ m
    (- ((1 : Int) * x 1 - 2)).pow' (2 * n) =
    ((1 : Int) * x 2 - (4 : Int) * x 1 + 4 ).pow' n

-- #check Int.pow

#print test
#check Nat.lcm

#reduce test 100
#check Int.add
set_option profiler true

set_option maxRecDepth 10000
example : test 10000 := by
  -- native_decide
  decide +kernel

example : test2 8000 := by
  decide +kernel

-- example : test' 10000 := by
--   decide +kernel

#reduce Nat.primesBelow 10

#check Float
#check 1 + 2 + 3

-- ex  ample : test2 10000 := by
--   -- native_decide
--   decide +kernel

-- 2000 180
-- 4000 659
-- 8000 2.71
-- 16000 11.8
-- 32000 58.1

-- 20000 19.9 0.30

#reduce 0 / 0

#check RatFunc

#reduce (100024 : Int) ^ 100024 - 1  = (100024 : Int) ^ 100024 - 1
