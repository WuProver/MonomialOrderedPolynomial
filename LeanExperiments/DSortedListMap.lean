import LeanExperiments.List

def DSortedListMap α (β : α → Type*)
    (cmp : α → α → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  { l : List ((k : α) × β k) // l.Chain' (cmp ·.1 ·.1 = .lt) }

namespace DSortedListMap

variable {α : Type*} {β : α → Type*} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Basic

abbrev toList (l : DSortedListMap α β cmp) := l.val

instance : Std.TransCmp (α := (k : α) × β k) (cmp ·.1 ·.1) where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans := Std.TransCmp.isLE_trans

instance : IsAntisymm (α := (k : α) × β k) (cmp ·.1 ·.1 = .lt) where
  antisymm _ _ h h' := by
    rw [Std.OrientedCmp.eq_swap (cmp := cmp)] at h
    simp [h'] at h

instance : IsIrrefl (α := (k : α) × β k) (cmp ·.1 ·.1 = .lt) where
  irrefl a := by
    simp [Std.ReflCmp.compare_self]

lemma chain' (l : DSortedListMap α β cmp) : l.val.Chain' (cmp ·.1 ·.1 = .lt) := l.property

lemma pairwise (l : DSortedListMap α β cmp) : l.val.Pairwise (cmp ·.1 ·.1 = .lt) :=
  List.chain'_iff_pairwise.mp l.chain'

lemma eq_iff (l₁ l₂ : DSortedListMap α β cmp) : l₁ = l₂ ↔ l₁.val = l₂.val := Subtype.eq_iff

instance : EmptyCollection <| DSortedListMap α β cmp := ⟨[], List.chain'_nil⟩

lemma empty_def : (∅ : DSortedListMap α β cmp) = ⟨[], List.chain'_nil⟩ := rfl

@[simp]
lemma empty_val : (∅ : DSortedListMap α β cmp).val = [] := rfl

lemma eq_empty_iff (l : DSortedListMap α β cmp) : l = ∅ ↔ l.val = [] := by
  rw [empty_def, show l = ⟨l.val, l.chain'⟩ from rfl]
  constructor <;> simp_intro ..

@[elab_as_elim]
theorem induction {motive : DSortedListMap α β cmp → Prop} (empty : motive ∅)
    (cons : ∀ (a : (k : α) × β k) (s : DSortedListMap α β cmp)
      (h : ∀ a', a' ∈ s.val → cmp a.1 a'.1 = .lt),
        motive s →
        motive ⟨a :: s.val, by
          simpa [List.chain'_iff_pairwise, s.pairwise]⟩)
    (s : DSortedListMap α β cmp) : motive s := by
  match h : s.val with
  | .nil => rw [← eq_empty_iff] at h; rwa [h]
  | .cons a l' =>
    have := s.chain'
    simp [h, List.chain'_iff_pairwise] at this
    rw [show s = ⟨s.val, s.chain'⟩ from rfl]
    simp_rw [h]
    letI s' : DSortedListMap α β cmp :=
      ⟨l', by simp [List.chain'_iff_pairwise, this]⟩
    apply cons a s' this.1
    apply induction empty cons
termination_by s.val.length
decreasing_by simp [h]

@[elab_as_elim]
theorem induction' {motive : DSortedListMap α β cmp → Prop} (empty : motive ∅)
    (cons : ∀ (a : α) (b : β a) (s : DSortedListMap α β cmp)
      (h : ∀ a' b', ⟨a', b'⟩ ∈ s.val → cmp a a' = .lt),
        motive s →
        motive ⟨⟨a, b⟩ :: s.val, by
          simpa [List.chain'_iff_pairwise, s.pairwise, Sigma.forall]⟩)
    (s : DSortedListMap α β cmp) : motive s :=
  induction empty (by simpa [Sigma.forall]) s

lemma find?_left_eq_some_iff (l : DSortedListMap α β cmp) (a : α) [∀ x, Decidable (x = a)]
    (b : (k : α) × (β k)) : l.val.find? (·.1 = a) = some b ↔ b ∈ l.val ∧ a = b.1 := by
  constructor
  · intro h
    have := List.find?_some h
    simp at this
    have := List.find?_left_eq_some_iff_of_pairwise' l.pairwise ⟨a, this ▸ b.2⟩ b
    simp [Std.LawfulEqCmp.compare_eq_iff_eq (cmp:=cmp)] at this
    simp [this] at h
    exact h
  · intro h
    have := List.find?_left_eq_some_iff_of_pairwise' l.pairwise ⟨a, h.2.symm ▸ b.2⟩ b
    simpa [Std.LawfulEqCmp.compare_eq_iff_eq (cmp:=cmp), ← h.2, h.1]

lemma find?_left_eq_some_iff' (l : DSortedListMap α β cmp) (a : (k : α) × (β k))
    [∀ x, Decidable (x = a.1)] : l.val.find? (·.1 = a.1) = some a ↔ a ∈ l.val := by
  have := l.find?_left_eq_some_iff a.1 a
  simpa

lemma find?_left_eq_some_iff'' (l : DSortedListMap α β cmp) (a : α) (b : β a)
    [∀ x, Decidable (x = a)] :
    l.val.find? (·.1 = a) = some ⟨a, b⟩ ↔ ⟨a, b⟩ ∈ l.val :=
  l.find?_left_eq_some_iff' ⟨a, b⟩

lemma mem_iff (l : DSortedListMap α β cmp) (a : (k : α) × (β k)) [∀ x, Decidable (x = a.1)] :
    a ∈ l.val ↔ l.val.find? (·.1 = a.1) = some a := l.find?_left_eq_some_iff' a |>.symm

lemma mem_iff' (l : DSortedListMap α β cmp) (a : α) (b : β a) [∀ x, Decidable (x = a)] :
    ⟨a, b⟩ ∈ l.val ↔ l.val.find? (·.1 = a) = some ⟨a, b⟩ :=
  l.find?_left_eq_some_iff' ⟨a, b⟩ |>.symm

lemma eq_of_mem' {l : DSortedListMap α β cmp} {a b1 b2}
    (h1 : ⟨a, b1⟩ ∈ l.val) (h2 : ⟨a, b2⟩ ∈ l.val) : b1 = b2 := by
  classical
  rw [mem_iff] at h1 h2
  simp [h1] at h2
  exact h2

lemma eq_of_mem {l : DSortedListMap α β cmp} {a1 a2} (h : a1.1 = a2.1)
    (h1 : a1 ∈ l.val) (h2 : a2 ∈ l.val) : a1 = a2 := by
  classical
  rw [Sigma.eq h]
  simp
  refine eq_of_mem' ?_ h2
  convert h1 using 2
  · exact h.symm
  · simp

def get? [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) : Option (β a) :=
    (List.findSome? (fun i ↦ if h : i.1 = a then some (h ▸ i.2 : β a) else none) l.val)

lemma find?_eq_get?_map [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) :
    l.val.find? (·.fst = a) = (l.get? a).map (⟨a, ·⟩) := by
  induction l using induction with
  | empty => simp [get?]
  | cons a s h m =>
    simp [get?] at m
    simp [get?, List.find?_cons, List.findSome?_cons]
    split
    · expose_names
      simp at heq
      subst heq
      simp
    · expose_names
      simp at heq
      simpa [heq]

def instFunLike [DecidableEq α] : DFunLike (DSortedListMap α β cmp) α (Option <| β ·) where
  coe := get?
  coe_injective' := by
    intro a b h
    rw [a.eq_iff]
    simp [funext_iff] at h
    apply List.Sorted.eq_of_mem_iff a.pairwise b.pairwise
    simp [mem_iff]
    intro x
    specialize h x.1
    constructor
    all_goals
      intro h'
      simp [find?_eq_get?_map, - List.map_findSome?] at *
      obtain ⟨a', h'⟩ := h'
      simp [h', eq_comm (b := some a')] at h
      use a'
      simp [h'.2, h]

lemma ext_iff [DecidableEq α] {l1 l2 : DSortedListMap α β cmp} :
    l1 = l2 ↔ ∀ s : α, l1.get? s = l2.get? s := instFunLike.ext_iff

@[ext]
lemma ext [DecidableEq α] {l1 l2 : DSortedListMap α β cmp} (h : ∀ s : α, l1.get? s = l2.get? s) :
    l1 = l2 := ext_iff.mpr h

@[simp]
def empty_get? [DecidableEq α] :
    (∅ : DSortedListMap α β cmp).get? = (fun _ ↦ none : (k : α) → Option <| β k) :=
  funext (fun _ ↦ rfl)

theorem get?_eq_none_iff' [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) :
    l.get? a = none ↔ l.val.find? (·.1 = a) = .none := by simp [get?]

theorem get?_eq_none_iff [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) :
    l.get? a = none ↔ ∀ b, ⟨a, b⟩ ∉ l.val := by
  simp [get?_eq_none_iff']
  constructor
  · intro h b h'
    exact h ⟨a, b⟩ h' rfl
  · intro h b h' h''
    apply h (h'' ▸ b.2)
    convert h'
    · exact h''.symm
    · simp

theorem get?_eq_some_iff_mem_val' [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) (b : β a) :
    l.get? a = some b ↔ ⟨a, b⟩ ∈ l.val := by
  simp [← find?_left_eq_some_iff', find?_eq_get?_map]

theorem get?_eq_some_iff_mem_val [DecidableEq α] (l : DSortedListMap α β cmp) (a : (k : α) × β k) :
    l.get? a.1 = some a.2 ↔ a ∈ l.val := get?_eq_some_iff_mem_val' l a.1 a.2

theorem get?_eq_some_iff_find?_eq_some [DecidableEq α] (l : DSortedListMap α β cmp)
    (a : α) (b : β a) : l.get? a = some b ↔ l.val.find? (·.1 = a) = some ⟨a, b⟩ := by
  simp [find?_eq_get?_map]

theorem get?_eq_of_mem [DecidableEq α] {l : DSortedListMap α β cmp} {i} (h : i ∈ l.val) :
    l.get? i.1 = i.2 := by
  simp [← l.find?_left_eq_some_iff', find?_eq_get?_map] at h
  obtain ⟨a, h⟩ := h
  exact h.2 ▸ h.1

private def example1 : DSortedListMap Int (fun _ ↦ Int) compare := ⟨[⟨1, 3⟩, ⟨2, 4⟩], by decide⟩

#reduce (example1.get? 2).get! + 2

#reduce example1.get? 1

#reduce example1.get? 3

-- instance : Zero (ListMap σ R cmp) where
--   zero := ∅

def keys (l : DSortedListMap α β cmp) : List α := l.val.map (·.1)

@[simp]
def keys_zero : (∅ : DSortedListMap α β cmp).keys = ∅ := rfl

lemma keys_pairwise (l : DSortedListMap α β cmp) : l.keys.Pairwise (cmp · · = .lt) :=
  List.pairwise_map.mpr l.pairwise

lemma mem_support_iff [DecidableEq α] (l : DSortedListMap α β cmp) (a : α) :
    a ∈ l.keys ↔ l.get? a ≠ none := by
  simp [← get?_eq_some_iff_mem_val, keys, ← Option.isSome_iff_ne_none, Option.isSome_iff_exists]

instance : IsAntisymm (α := α) (cmp · · |>.isLE) where
  antisymm _ _ h h' := Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h h')

instance : IsAntisymm (α := α) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

instance : IsTrans (α := α) (cmp · · |>.isLE) where
  trans _ _ _ := Std.TransCmp.isLE_trans

instance : IsTrans (α := α) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

instance : IsTotal (α := α) (cmp · · |>.isLE) where
  total a b := by
    rw [or_iff_not_imp_left]
    intro h
    simp [Std.OrientedCmp.lt_of_not_isLE h]

instance : IsTotal (α := α) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

variable (cmp) in
def linearOrder [DecidableRel (cmp · · |>.isLE)] : LinearOrder α where
  le := (cmp · · |>.isLE)
  le_refl _ := Std.ReflCmp.isLE_rfl
  le_trans _ _ _ a b := Std.TransCmp.isLE_trans a b
  le_antisymm _ _ h h' := Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h h')
  le_total := (inferInstanceAs <| IsTotal (α := α) (cmp · · |>.isLE)).total
  toDecidableLE := inferInstance

variable (cmp) in
def onKeys (f : (k : α) → Option <| β k) (s : Finset α) (h : ∀ x, x ∈ s ↔ f x ≠ none) :
    DSortedListMap α β cmp :=
  ⟨s.sort (cmp · · |>.isLE) |>.attach.map fun x ↦ ⟨x.1,
      (f x.1).get <| Option.isSome_iff_ne_none.mpr <| (h x.1).mp <| (Finset.mem_sort _).mp x.2⟩,
    by
      simp [List.chain'_map, ← List.chain'_map Subtype.val (R := (cmp · · = Ordering.lt))]
      simp [List.chain'_iff_pairwise]
      letI := linearOrder cmp
      convert s.sort_sorted_lt with a b
      refine _root_.trans (b := (cmp a b).isLE ∧ ¬ (cmp b a).isLE) ?_ (Iff.refl _)
      simp [Std.OrientedCmp.gt_iff_lt]
      simp [Ordering.isLE_iff_ne_gt]
      simp_intro ..
  ⟩

def get?_onKeys [DecidableEq α] {f : (k : α) → Option <| β k} {s h} :
    (onKeys cmp f s h).get? = f := by
  funext x
  have h' := h x
  by_cases hx : x ∈ s
  · simp [hx, Option.ne_none_iff_exists'] at h'
    obtain ⟨y, h'⟩ := h'
    simp [onKeys, get?_eq_some_iff_mem_val', hx, h']
  · simp [hx] at h'
    simp [h', onKeys, get?_eq_none_iff, hx]

end Basic

section mergeWith

variable (mergeFn : (a : α) → β a → β a → Option (β a))

def mergeFn' (a : (k : α) × β k) (b : (k : α) × β k) (h : cmp a.1 b.1 = .eq) :
    Option ((k : α) × β k) :=
  mergeFn a.1 a.2 ((Std.LawfulEqCmp.eq_of_compare h).symm ▸ b.2) |>.map (⟨a.1, ·⟩)

instance : Fact <|
    ∀ a b : (k : α) × β k,
      (h : cmp a.1 b.1 = Ordering.eq) → ∀ a' ∈ mergeFn' mergeFn a b h, cmp a.1 a'.1 = .eq where
  out a b h a' ha' := by
    simp [mergeFn'] at ha'
    obtain ⟨_, ha'⟩ := ha'
    rw [← Sigma.eta a'] at ha'
    simp [- Sigma.eta] at ha'
    exact Std.ReflCmp.cmp_eq_of_eq ha'.2.1

def mergeWith (l₁ l₂ : DSortedListMap α β cmp) : DSortedListMap α β cmp :=
  ⟨List.mergeWithByFuel l₁.val l₂.val (cmp ·.1 ·.1) (mergeFn' mergeFn), by
    rw [List.chain'_iff_pairwise, List.mergeWithByFuel_eq]
    apply List.mergeWith_pairwise_of_pairwise
    · rw [← List.chain'_iff_pairwise]; exact l₁.property
    · rw [← List.chain'_iff_pairwise]; exact l₂.property⟩

lemma mergeWith_def (l₁ l₂ : DSortedListMap α β cmp) :
    (l₁.mergeWith mergeFn l₂).val =
      List.mergeWith l₁.val l₂.val (cmp ·.1 ·.1) (mergeFn' mergeFn) := by
  rw [← List.mergeWithByFuel_eq]
  rfl

theorem _root_.Sigma.eq_of_eq {α : Type*} {β : α → Type*} {p : Σ a, β a} {a : α} (h : p.1 = a) :
    p = ⟨a, h ▸ p.2⟩ := by
  apply Sigma.eq
  rfl

set_option maxHeartbeats 4000000 in
lemma mergeWith_get? [DecidableEq α] (l₁ l₂ : DSortedListMap α β cmp) (x : α) :
    (l₁.mergeWith mergeFn l₂).get? x =
      match l₁.get? x, l₂.get? x with
      | some y, none => some y
      | none, some y => some y
      | some y₁, some y₂ => mergeFn x y₁ y₂
      | none, none => none := by
  classical
  split
  · expose_names
    simp [get?_eq_some_iff_mem_val'] at heq
    simp [get?_eq_none_iff] at heq_1
    simp [get?_eq_some_iff_mem_val',
      mergeWith_def, List.mem_mergeWith_iff l₁.pairwise l₂.pairwise,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    simp [show ∃ y, ⟨x, y⟩ ∈ l₁.val from ⟨y, heq⟩,
      show ¬ ∃ y, ⟨x, y⟩ ∈ l₂.val by simp [heq_1]]
    intro x' hx' hxx'
    exact eq_of_mem hxx' heq hx'
  · expose_names
    simp [get?_eq_some_iff_mem_val'] at heq_1
    simp [get?_eq_none_iff] at heq
    simp [get?_eq_some_iff_mem_val',
      mergeWith_def, List.mem_mergeWith_iff l₁.pairwise l₂.pairwise,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    simp [show ∃ y, ⟨x, y⟩ ∈ l₂.val from ⟨y, heq_1⟩,
      show ¬ ∃ y, ⟨x, y⟩ ∈ l₁.val by simp [heq]]
    intro x' hx' hxx'
    exact eq_of_mem hxx' heq_1 hx'
  · expose_names
    simp [get?_eq_some_iff_mem_val'] at heq heq_1
    rcases h : (mergeFn x y₁ y₂) with none | y
    · simp [get?_eq_none_iff',
        mergeWith_def, List.mem_mergeWith_iff l₁.pairwise l₂.pairwise,
        Std.LawfulEqCmp.compare_eq_iff_eq]
      simp [imp_not_comm]
      intro x' hx'
      have := fun (y : β x'.1) ↦ Sigma.eq_of_eq (show (⟨x'.1, y⟩ : Sigma β).1 = x from hx')
      simp [this, Eq.rec_eq_cast, (cast_bijective (congrArg β hx'.symm)).surjective.exists, hx']
      simp [show ∃ y, ⟨x, y⟩ ∈ l₁.val from ⟨y₁, heq⟩,
        show ∃ y, ⟨x, y⟩ ∈ l₂.val from ⟨y₂, heq_1⟩]
      use x, y₁
      simp [heq]
      use x, y₂
      simp [heq_1, mergeFn', h]
    · simp [get?_eq_some_iff_mem_val',
        mergeWith_def, List.mem_mergeWith_iff l₁.pairwise l₂.pairwise,
        Std.LawfulEqCmp.compare_eq_iff_eq]
      simp [show ∃ y, ⟨x, y⟩ ∈ l₁.val from ⟨y₁, heq⟩,
        show ∃ y, ⟨x, y⟩ ∈ l₂.val from ⟨y₂, heq_1⟩]
      intro x₁ hx₁ hxx₁ x₂ hx₂ hxx₂
      have := eq_of_mem hxx₁ heq hx₁
      simp [← eq_of_mem hxx₁ heq hx₁, ← eq_of_mem hxx₂ heq_1 hx₂]
      simp [mergeFn', h]
  · expose_names
    simp [get?_eq_none_iff] at heq heq_1
    simp [get?_eq_none_iff',
      mergeWith_def, List.mem_mergeWith_iff l₁.pairwise l₂.pairwise,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    simp [imp_not_comm]
    intro x' hx'
    have := fun (y : β x'.1) ↦ Sigma.eq_of_eq (show (⟨x'.1, y⟩ : Sigma β).1 = x from hx')
    simp [this, Eq.rec_eq_cast, (cast_bijective (congrArg β hx'.symm)).surjective.exists]
    simp [show ¬ ∃ y, ⟨x, y⟩ ∈ l₁.val by simp [heq],
      show ¬ ∃ y, ⟨x, y⟩ ∈ l₂.val by simp [heq_1]]

private def example2 : DSortedListMap Int (fun _ ↦ Int) compare :=
  ⟨[⟨1, 5⟩, ⟨3, 4⟩], by decide +kernel⟩

#reduce example1.mergeWith (fun _ ↦ (some <| · + ·)) example2

end mergeWith
