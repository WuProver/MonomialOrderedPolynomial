import LeanExperiments.MvPolynomial
import LeanExperiments.List

def SortedFinsupp σ R
    [Zero R] (cmp : σ → σ → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  { l : List (σ × R) // l.Chain' (cmp ·.1 ·.1 = .lt) ∧ ∀ i ∈ l, i.2 ≠ 0 }

namespace SortedFinsupp

section

variable {R : Type*} [Zero R]

variable {σ : Type*} {cmp : σ → σ → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

instance : Std.TransCmp (α := σ × R) (cmp ·.1 ·.1) where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans := Std.TransCmp.isLE_trans

instance : IsAntisymm (α := (σ × R)) (cmp ·.1 ·.1 = .lt) where
  antisymm _ _ h h' := by
    rw [Std.OrientedCmp.eq_swap (cmp := cmp)] at h
    simp [h'] at h

instance : IsIrrefl (α := (σ × R)) (cmp ·.1 ·.1 = .lt) where
  irrefl a := by
    simp [Std.ReflCmp.compare_self]

lemma ne_zero {l : SortedFinsupp σ R cmp} {i : (σ × R)} (h : i ∈ l.val) : i.2 ≠ 0 := l.2.2 i h

lemma ne_zero' {l : SortedFinsupp σ R cmp} {a : σ} {b : R} (h : (a, b) ∈ l.val) : b ≠ 0 := ne_zero h

lemma chain' (l : SortedFinsupp σ R cmp) : l.val.Chain' (cmp ·.1 ·.1 = .lt) := l.2.1

lemma pairwise (l : SortedFinsupp σ R cmp) : l.val.Pairwise (cmp ·.1 ·.1 = .lt) :=
  List.chain'_iff_pairwise.mp l.chain'


instance : EmptyCollection (SortedFinsupp σ R cmp) where
  emptyCollection := ⟨[], ⟨List.chain'_nil, by simp⟩⟩

lemma empty_eq : (∅ : SortedFinsupp σ R cmp) = ⟨[], ⟨List.chain'_nil, by simp⟩⟩ := rfl

lemma empty_iff (l : SortedFinsupp σ R cmp) : l = ∅ ↔ l.val = [] := by
  rw [empty_eq, show l = ⟨l.val, l.2⟩ from rfl]
  constructor <;> simp_intro ..

@[elab_as_elim]
theorem induction {motive : SortedFinsupp σ R cmp → Prop} (empty : motive ∅)
    (cons : ∀ (a : σ) (b : R) (s : SortedFinsupp σ R cmp)
      (h : ∀ a' b', (a', b') ∈ s.val → cmp a a' = .lt) (h' : b ≠ 0),
        motive s →
        motive ⟨(a, b) :: s.val, by
          simp [List.chain'_iff_pairwise, s.pairwise, h']; exact ⟨h, fun _ _ ↦ ne_zero'⟩⟩)
    (s : SortedFinsupp σ R cmp) : motive s := by
  match h : s.val with
  | .nil => rw [← empty_iff] at h; rwa [h]
  | .cons (a, b) l' =>
    have := s.2
    simp [h, List.chain'_iff_pairwise] at this
    rw [show s = ⟨s.1, s.2⟩ from rfl]
    simp_rw [h]
    letI s' : SortedFinsupp σ R cmp :=
      ⟨l', by simp! [List.chain'_iff_pairwise, this]; exact this.2.2⟩
    apply cons a b s' this.1.1 this.2.1
    apply induction empty cons
termination_by s.val.length
decreasing_by simp [h]

lemma find?_left_eq_some_iff (l : SortedFinsupp σ R cmp) (a : σ) [∀ x, Decidable (x = a)] (b : σ × R) :
    (l.val.find? (·.1 = a)) = some b ↔ b ∈ l.val ∧ a = b.1 := by
  have := (List.find?_left_is_some_iff_of_pairwise' l.pairwise (a, b.2) b)
  simpa [Std.LawfulEqCmp.compare_eq_iff_eq (cmp:=cmp)]

lemma find?_left_eq_some_iff' (l : SortedFinsupp σ R cmp) (a : σ × R) [∀ x, Decidable (x = a.1)] :
    (l.val.find? (·.1 = a.1)) = some a ↔ a ∈ l.val := by
  have := l.find?_left_eq_some_iff a.1 a
  simpa

lemma find?_left_eq_some_iff'' (l : SortedFinsupp σ R cmp) (a : σ) (b : R) [∀ x, Decidable (x = a)] :
    (l.val.find? (·.1 = a)) = some (a, b) ↔ (a, b) ∈ l.val := l.find?_left_eq_some_iff' (a, b)

instance instFunLike [DecidableEq σ] : FunLike (SortedFinsupp σ R cmp) σ R where
  coe l a := (List.find? (·.1 = a) l.val).elim 0 (·.2)
  coe_injective' := by
    intro a b h
    rw [a.eq_iff]
    simp [funext_iff] at h
    contrapose! h
    apply mt <| List.Sorted.eq_of_mem_iff a.pairwise b.pairwise at h
    simp at h
    obtain ⟨x, y, h⟩ := h
    use x
    by_cases h' : ⟨x, y⟩ ∈ a.val
    · simp [h'] at h
      intro h''
      simp [a.find?_left_eq_some_iff x (x, y) |>.mpr ⟨h', rfl⟩, Option.elim] at h''
      split at h''
      rotate_left
      · exact a.ne_zero h' h''
      expose_names
      simp [b.find?_left_eq_some_iff x x_4] at heq
      rw [h'', heq.2] at h
      exact h heq.1
    · simp [h'] at h
      intro h''
      simp [b.find?_left_eq_some_iff x (x, y) |>.mpr ⟨h, rfl⟩, Option.elim] at h''
      split at h''
      rotate_left
      · exact b.ne_zero h h''.symm
      expose_names
      simp [a.find?_left_eq_some_iff x x_4] at heq
      rw [← h'', heq.2] at h'
      exact h' heq.1

@[simp]
def empty_coe_eq [DecidableEq σ] :
    (∅ : SortedFinsupp σ R cmp) = (fun _ ↦ 0 : σ → R) := funext (fun _ ↦ rfl)

lemma apply_def [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    l a = (List.find? (·.1 = a) l.val).elim 0 (·.2) := rfl

lemma _root_.Option.elim_ne_d {α β} {b : β} {p : α → β} {a : Option α} (h : a.elim b p ≠ b) :
    a ≠ none := by
  aesop

lemma _root_.Option.elim_ne_d' {α β} {b : β} {p : α → β} {a : Option α} (h : a.elim b p ≠ b) :
    ∃ a' : α, a = some a' := by
  simp [← Option.ne_none_iff_exists', a.elim_ne_d h]

theorem apply_eq_zero_iff' [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    l a = 0 ↔ (a, l a) ∉ l.val := by
  rw [apply_def]
  constructor
  · simp_intro _ h
    exact l.ne_zero h rfl
  · intro h
    contrapose! h
    obtain ⟨a', ha'⟩ := Option.elim_ne_d' h
    simp [ha']
    simp [l.find?_left_eq_some_iff] at ha'
    simp [ha']

theorem apply_eq_zero_iff [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    l a = 0 ↔ ∀ b, (a, b) ∉ l.val := by
  constructor
  · intro h b h'
    have := l.ne_zero h'
    rw [← l.find?_left_eq_some_iff'] at h'
    simp [apply_def, h'] at h
    exact this h
  · intro h
    exact l.apply_eq_zero_iff' a |>.mpr <| h (l a)

theorem apply_ne_zero_iff [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    l a ≠ 0 ↔ ∃ b, (a, b) ∈ l.val := by simp [l.apply_eq_zero_iff a]

theorem apply_ne_zero_iff' [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    l a ≠ 0 ↔ (a, l a) ∈ l.val := (l.apply_eq_zero_iff' a).not_left

private def example1 : SortedFinsupp Int Rat compare := ⟨[(1, 3), (2, 4)], by decide⟩

#check AddEquivClass

#eval ((example1 : Int → Rat) 2) + 2

#eval example1 1

#eval example1 3

-- instance : Zero (SortedFinsupp σ R cmp) where
--   zero := ∅

def support (l : SortedFinsupp σ R cmp) : List σ := l.val.map (·.1)

@[simp]
def support_empty : (∅ : SortedFinsupp σ R cmp).support = ∅ := rfl

lemma support_pairwise (l : SortedFinsupp σ R cmp) : l.support.Pairwise (cmp · · = .lt) :=
  List.pairwise_map.mpr l.pairwise

lemma mem_support_iff [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    a ∈ l.support ↔ l a ≠ 0 := by
  simp [apply_ne_zero_iff, support]

lemma toFinset_support [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    l.support.toFinset = Function.support l := by
  induction l using induction with
  | empty => simp [empty_coe_eq]
  | cons a b s h h' h'' =>
    simp [support]
    sorry

lemma support_finite [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    (Function.support l).Finite := by simp [← toFinset_support]

#check Finsupp.instFunLike
-- def ofFun [DecidableEq σ] (s : ) :
-- #check Finsupp.mem_support

def equiv_finsupp [DecidableEq σ] : Equiv (SortedFinsupp σ R cmp) (σ →₀ R) where
  toFun f := Finsupp.ofSupportFinite f f.support_finite
  invFun f :=

end

def mergeAdd (a₁ a₂ : σ × R) := let a := a₁.2 + a₂.2; if a = 0 then Option.none else Option.some (a₁.1, a)

instance : Fact <| ∀ a b : σ × R, cmp a.1 b.1 = Ordering.eq → ∀ a' ∈ mergeAdd a b, cmp a.1 a'.1 = .eq where
  out := by
    intro a b h a' ha'
    simp [mergeAdd] at ha'
    simp [← ha'.2, Std.ReflCmp.cmp_eq_of_eq]

variable (cmp) in
def add' (l₁ : List (σ × R)) (l₂ : List (σ × R)) := List.mergeWithByFuel l₁ l₂ (cmp ·.1 ·.1) mergeAdd

instance instAdd : Add (SortedFinsupp σ R cmp) where
  add l₁ l₂ := ⟨
    add' cmp l₁.val l₂.val,
    by
      constructor
      · rw [add', List.chain'_iff_pairwise, List.mergeWithByFuel_eq]
        apply List.mergeWith_pairwise_of_pairwise
        · rw [← List.chain'_iff_pairwise]; exact l₁.property.1
        · rw [← List.chain'_iff_pairwise]; exact l₂.property.1
      · simp [add']
        intro a b h hb
        simp [List.mergeWithByFuel_eq,
          List.mem_mergeWith_iff l₁.pairwise l₂.pairwise mergeAdd,
          hb, mergeAdd, Std.LawfulEqCmp.compare_eq_iff_eq] at h
        split_ifs at h with h' h''
        · obtain ⟨x', hx', h'⟩ := h'
          obtain ⟨x'', hx'', h''⟩ := h''
          specialize h x'.1 x'.2 hx' (Std.LawfulEqCmp.eq_of_compare h') x''.1 x''.2 hx''
            (Std.LawfulEqCmp.eq_of_compare h'')
          aesop
        · obtain ⟨x', hx', h'⟩ := h'
          specialize h x'.1 x'.2 hx' (Std.LawfulEqCmp.eq_of_compare h')
          exact l₁.ne_zero hx' h.2.symm
        · obtain ⟨⟨b, hb⟩, h⟩ := h
          specialize h a b hb rfl
          exact l₂.ne_zero hb h.2.symm
    ⟩

-- instance : AddEquivClass

def addEquiv : SortedFinsupp σ R cmp ≃+ (σ →₀ R) where
  toFun := Finsupp.ofSupportFinite

private def example2 : SortedFinsupp Nat Rat compare := ⟨[(1, 5), (3, 4)], by decide⟩

#eval example1 + example2

def mulMon' [Add σ] (n : σ) (k : R) (l : List (σ × R)) : List (σ × R) :=
  l.filterMap (fun a ↦ let a' := k * a.2; if a' = 0 then .none else .some (a.1 + n, a'))


def chain'_mulMon' (k : R) (l : List (σ × R)) (h : l.Chain' (cmp ·.1 ·.1 = .lt)) : (mulMon' k l).Chain' (cmp ·.1 ·.1 = .lt) := by
  induction l with
  | nil => simp [mulMon']
  | cons head tail h' =>
    simp [mulMon', List.chain'_cons'] at *
    sorry

def mulMon (k : R) (l : SortedFinsupp σ R cmp) : SortedFinsupp σ R cmp := ⟨mulMon' k l.val, by
  exact chain'_mulMon' k l.val l.property
  sorry
⟩

def mul' (p₁ : List (σ × R)) (p₂ : List (σ × R)) [∀ k : R, Decidable (k = 1)] : List (σ × R) :=
  let p₁l := p₁.lengthTR
  let p₂l := p₂.lengthTR
  let fuel := p₁l * p₂l + 1
  if p₁l < p₂l then
    go p₁ p₂ fuel []
  else
    go p₂ p₁ fuel []
where
  go (p₁ : List (σ × R)) (p₂ : List (σ × R)) (fuel : Nat) (acc : List (σ × R)) : List (σ × R) :=
    match p₁ with
    | .nil => acc
    | .cons (k, m) p₁ => go p₁ p₂ fuel (add' (p₂.mulMon k m cmp) cmp (fuel := fuel))


instance : Mul (SortedFinsupp σ R cmp) where
  mul := sorry


#check Finsupp
