import LeanSortedFinsupp.List
import LeanSortedFinsupp.DSortedListMap

def DSortedFinsupp σ (R : σ → Type*)
    [∀ k, Zero (R k)] (cmp : σ → σ → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  { l : DSortedListMap σ R cmp // ∀ a ∈ l.val, a.2 ≠ 0}

#check DFinsupp
#check DirectSum

namespace DSortedFinsupp

variable {σ : Type*} {cmp : σ → σ → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {R : σ → Type*} [∀ k, Zero (R k)]

section Basic

instance [DecidableEq σ] [∀ a : σ, DecidableEq (R a)] : DecidableEq (DSortedFinsupp σ R cmp) :=
  Subtype.instDecidableEq

@[inline]
abbrev toList (l : DSortedFinsupp σ R cmp) := l.val.val

lemma chain' (l : DSortedFinsupp σ R cmp) : l.toList.Chain' (cmp ·.1 ·.1 = .lt) := l.val.2

lemma pairwise (l : DSortedFinsupp σ R cmp) : l.toList.Pairwise (cmp ·.1 ·.1 = .lt) :=
  List.chain'_iff_pairwise.mp l.chain'

lemma ne_zero {l : DSortedFinsupp σ R cmp} {i : Sigma R} (h : i ∈ l.toList) : i.2 ≠ 0 := l.2 i h

lemma ne_zero' {l : DSortedFinsupp σ R cmp} {a : σ} {b : R a} (h : ⟨a, b⟩ ∈ l.toList) : b ≠ 0 := ne_zero h

lemma ne_zero_of_val_get?_eq_some [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {a : σ} {b : R a}
    (h : l.val.get? a = some b) : b ≠ 0 := ne_zero' ((l.val.get?_eq_some_iff_mem_val' ..).mp h)

lemma val_get?_ne_some_zero [DecidableEq σ] {l : DSortedFinsupp σ R cmp} (a : σ) :
    l.val.get? a ≠ some 0 := by
  by_contra h
  exact l.ne_zero_of_val_get?_eq_some h rfl

lemma eq_iff (l₁ l₂ : DSortedFinsupp σ R cmp) : l₁ = l₂ ↔ l₁.val = l₂.val := Subtype.eq_iff

instance : Zero (DSortedFinsupp σ R cmp) where
  zero := ⟨⟨[], List.chain'_nil⟩, by simp⟩

lemma zero_def : (0 : DSortedFinsupp σ R cmp) = ⟨⟨[], List.chain'_nil⟩, by simp⟩ := rfl

lemma eq_zero_iff (l : DSortedFinsupp σ R cmp) : l = 0 ↔ l.val = ∅ := by
  rw [l.eq_iff]
  rfl

@[inline]
abbrev mk' (val : DSortedListMap σ R cmp) (h : open Classical in ∀ a, val.get? a ≠ some 0) :
    DSortedFinsupp σ R cmp :=
  ⟨val, by
    open Classical in simp [val.get?_eq_some_iff_mem_val'] at h
    aesop
  ⟩

-- @[elab_as_elim]
-- theorem induction {motive : DSortedFinsupp σ R cmp → Prop} (zero : motive 0)
--     (cons : ∀ (a : σ × R) (s : DSortedFinsupp σ R cmp)
--       (h : ∀ a', a' ∈ s.val → cmp a.1 a'.1 = .lt) (h' : a.2 ≠ 0),
--         motive s →
--         motive ⟨a :: s.val, by
--           simp [List.chain'_iff_pairwise, s.pairwise, h'] at *; exact ⟨h, fun _ _ ↦ ne_zero'⟩⟩)
--     (s : DSortedFinsupp σ R cmp) : motive s := by
--   match h : s.val with
--   | .nil => rw [← eq_zero_iff] at h; rwa [h]
--   | .cons a l' =>
--     have := s.2
--     simp [-Prod.forall, h, List.chain'_iff_pairwise] at this
--     rw [show s = ⟨s.1, s.2⟩ from rfl]
--     simp_rw [h]
--     letI s' : DSortedFinsupp σ R cmp :=
--       ⟨l', by simp [-Prod.forall, List.chain'_iff_pairwise, this]; exact this.2.2⟩
--     apply cons a s' this.1.1 this.2.1
--     apply induction zero cons
-- termination_by s.val.length
-- decreasing_by simp [h]

-- @[elab_as_elim]
-- theorem induction' {motive : DSortedFinsupp σ R cmp → Prop} (zero : motive 0)
--     (cons : ∀ (a : σ) (b : R) (s : DSortedFinsupp σ R cmp)
--       (h : ∀ a' b', (a', b') ∈ s.val → cmp a a' = .lt) (h' : b ≠ 0),
--         motive s →
--         motive ⟨(a, b) :: s.val, by
--           simp [List.chain'_iff_pairwise, s.pairwise, h']; exact ⟨h, fun _ _ ↦ ne_zero'⟩⟩)
--     (s : DSortedFinsupp σ R cmp) : motive s :=
--   induction zero (by simpa) s

-- lemma find?_left_eq_some_iff (l : DSortedFinsupp σ R cmp) (a : σ) [∀ x, Decidable (x = a)] (b : σ × R) :
--     l.val.find? (·.1 = a) = some b ↔ b ∈ l.val ∧ a = b.1 := by
--   have := (List.find?_left_eq_some_iff_of_pairwise' l.pairwise (a, b.2) b)
--   simpa [Std.LawfulEqCmp.compare_eq_iff_eq (cmp:=cmp)]

-- lemma find?_left_eq_some_iff' (l : DSortedFinsupp σ R cmp) (a : σ × R) [∀ x, Decidable (x = a.1)] :
--     l.val.find? (·.1 = a.1) = some a ↔ a ∈ l.val := by
--   have := l.find?_left_eq_some_iff a.1 a
--   simpa

-- lemma find?_left_eq_some_iff'' (l : DSortedFinsupp σ R cmp) (a : σ) (b : R) [∀ x, Decidable (x = a)] :
--     l.val.find? (·.1 = a) = some (a, b) ↔ (a, b) ∈ l.val := l.find?_left_eq_some_iff' (a, b)

-- lemma mem_iff (l : DSortedFinsupp σ R cmp) (a : σ × R) [∀ x, Decidable (x = a.1)] :
--     a ∈ l.val ↔ l.val.find? (·.1 = a.1) = some a := l.find?_left_eq_some_iff' a |>.symm

-- lemma mem_iff' (l : DSortedFinsupp σ R cmp) (a : σ) (b : R) [∀ x, Decidable (x = a)] :
--     (a, b) ∈ l.val ↔ l.val.find? (·.1 = a) = some (a, b) := l.find?_left_eq_some_iff' (a, b) |>.symm

-- lemma eq_of_mem {l : DSortedFinsupp σ R cmp} {a b1 b2}
--     (h1 : (a, b1) ∈ l.val) (h2 : (a, b2) ∈ l.val) : b1 = b2 := by
--   classical
--   rw [mem_iff] at h1 h2
--   simp [h1] at h2
--   exact h2

lemma _root_.Option.elim_ne_d {α R'} {b : R'} {p : α → R'} {a : Option α} (h : a.elim b p ≠ b) :
    a ≠ none := by
  aesop

lemma _root_.Option.elim_ne_d' {α R'} {b : R'} {p : α → R'} {a : Option α} (h : a.elim b p ≠ b) :
    ∃ a' : α, a = some a' := by
  simp [← Option.ne_none_iff_exists', a.elim_ne_d h]

lemma _root_.Option.ne_none_of_getD_ne_dflt {α} {dflt : α} {a : Option α} (h : a.getD dflt ≠ dflt) :
    a ≠ none := by
  aesop

lemma _root_.Option.isSome_of_getD_ne_dflt {α} {dflt : α} {a : Option α} (h : a.getD dflt ≠ dflt) :
    a.isSome := a.isSome_iff_ne_none.mpr <| a.ne_none_of_getD_ne_dflt h

lemma _root_.Option.eq_some_get_of_getD_ne_dflt {α} {dflt : α} {a : Option α} (h : a.getD dflt ≠ dflt) :
    a = some (a.get <| Option.isSome_of_getD_ne_dflt h) := by
  simp

lemma _root_.Option.eq_some_get_of_getD_ne_dflt' {α} {dflt : α} {a : Option α} {b : α}
    (h : a.getD dflt = b) (h' : b ≠ dflt) :
    a = some b := by
  simp [a.getD_eq_iff, h'.symm] at h
  exact h

lemma _root_.Option.eq_some_of_getD_ne_dflt {α} {dflt : α} {a : Option α} (h : a.getD dflt ≠ dflt) :
    ∃ a' : α, a = some a' := ⟨_, _root_.Option.eq_some_get_of_getD_ne_dflt h⟩

instance instDFunLike [DecidableEq σ] : DFunLike (DSortedFinsupp σ R cmp) σ R where
  coe l a := (l.val.get? a).getD 0
  coe_injective' := by
    intro a b h
    rw [a.eq_iff]
    simp [funext_iff] at h
    ext x y
    specialize h x
    constructor
    all_goals
      intro h'
      simp [h', eq_comm (b := y)] at h
      -- have := h ▸ h'
      have := Option.eq_some_get_of_getD_ne_dflt <| h ▸ ne_zero_of_val_get?_eq_some h'
      rw [this, Option.getD] at h
      rw [this, h.symm]

lemma ext_iff [DecidableEq σ] {l1 l2 : DSortedFinsupp σ R cmp} :
    l1 = l2 ↔ ∀ s : σ, l1 s = l2 s := DFunLike.ext_iff

@[ext]
lemma ext [DecidableEq σ] {l1 l2 : DSortedFinsupp σ R cmp} (h : ∀ s : σ, l1 s = l2 s) :
    l1 = l2 := ext_iff.mpr h

@[simp]
lemma zero_apply [DecidableEq σ] (x : σ) :
    (0 : DSortedFinsupp σ R cmp) x = 0 := rfl

lemma eq_zero_iff_apply_eq_zero [DecidableEq σ] (l : DSortedFinsupp σ R cmp) :
    l = 0 ↔ ∀ x : σ, l x = 0 := by
  rw [ext_iff]
  rfl

lemma apply_def [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    l a = (l.val.get? a).getD 0 := rfl

variable (cmp) in
def single (x : σ) (y : R x) [Decidable (y = 0)] : DSortedFinsupp σ R cmp :=
  if h : y = 0 then 0 else
    mk' (DSortedListMap.single cmp x y) (by
      simp [DSortedListMap.single_get?]
      aesop)

lemma single_apply [DecidableEq σ] (a : σ) (b : R a) [Decidable (b = 0)] (c : σ) :
    (single cmp a b) c = if h : a = c then h ▸ b else 0 := by
  simp [apply_def, single]
  split
  · simp [zero_def, DSortedListMap.get?]
    aesop
  · simp [DSortedListMap.single_get?]
    split
    · simp
    · simp

lemma single_get?' [DecidableEq σ] (a : σ) (b : R a) [Decidable (b = 0)] :
    (single cmp a b) a = b := by
  simp [single_apply]

lemma single_get?_of_ne [DecidableEq σ] (a : σ) (b : R a) [Decidable (b = 0)] (c : σ) (h : a ≠ c) :
    (single cmp a b) c = 0 := by
  simp [single_apply, h]

theorem apply_eq_zero_iff_val_get?_eq_none [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    l a = 0 ↔ l.val.get? a = none := by
  rw [apply_def]
  constructor
  · intro this
    simpa [Option.getD_eq_iff, l.val_get?_ne_some_zero a]
  · simp_intro ..

theorem apply_eq_zero_iff_get?_val_ne_some_apply [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    l a = 0 ↔ l.val.get? a ≠ some (l a) := by
  constructor
  · simp_intro .. [apply_eq_zero_iff_val_get?_eq_none]
  · intro h
    simp [apply_def] at *
    contrapose! h
    apply Option.eq_some_get_of_getD_ne_dflt at h
    nth_rw 2 [h]
    rwa [Option.getD_some]

lemma apply_eq_zero_iff_not_mem_val_keys [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    l a = 0 ↔ a ∉ l.val.keys := by
  simp [l.val.mem_keys_iff, apply_eq_zero_iff_val_get?_eq_none]

-- theorem apply_ne_zero_iff [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
--     l a ≠ 0 ↔ ∃ (b : R a), l.val.get? a = .some := by simp [l.apply_eq_zero_iff a]

theorem apply_ne_zero_iff_get?_val_eq_some_apply [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    l a ≠ 0 ↔ l.val.get? a = some (l a) := (l.apply_eq_zero_iff_get?_val_ne_some_apply a).not_left

-- theorem apply_eq_of_mem [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {i} (h : i ∈ l.val) :
--     l i.1 = i.2 := by
--   rw [← l.find?_left_eq_some_iff'] at h
--   simp [apply_def, h]

theorem apply_eq_iff_of_apply_ne_zero [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {x : σ}
    {y : R x} (h : l x ≠ 0) : l x = y ↔ l.val.get? x = some y := by
  simp [apply_ne_zero_iff_get?_val_eq_some_apply] at h
  simp [h]

theorem apply_eq_of_get?_val_eq_some [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {x : σ} {y : R x}
    (h : l.val.get? x = some y) : l x = y := by simp [apply_def, h]

theorem get?_val_eq_some_iff [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {x : σ} {y : R x} :
    l.val.get? x = some y ↔ l x = y ∧ y ≠ 0 := by
  constructor
  · intro h
    exact ⟨apply_eq_of_get?_val_eq_some h, ne_zero_of_val_get?_eq_some h⟩
  · intro ⟨h1, h2⟩
    rw [apply_def] at h1
    apply Option.eq_some_get_of_getD_ne_dflt' h1 at h2
    exact h2

-- theorem apply_eq_iff_of_apply_ne_zero' [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {x : σ} (y : R)
--     (h : y ≠ 0) : l x = y ↔ (x, y) ∈ l.val := by
--   constructor
--   · intro h'
--     exact apply_eq_iff_of_apply_ne_zero y (h'.symm ▸ h) |>.mp h'
--   · intro h'
--     exact apply_eq_of_mem h'

-- theorem apply_eq_of_mem' [DecidableEq σ] {l : DSortedFinsupp σ R cmp} {a b} (h : (a, b) ∈ l.val) :
--     l a = b := apply_eq_of_mem h

private def example1 : DSortedFinsupp Int (fun _ ↦ Int) compare := ⟨⟨[⟨1, 3⟩, ⟨2, 4⟩], by decide⟩, by decide⟩

#reduce (example1 : Int → Int) 2 + 2

#reduce example1 1

#reduce example1 3

-- instance : Zero (DSortedFinsupp σ R cmp) where
--   zero := ∅

def support (l : DSortedFinsupp σ R cmp) : List σ := l.val.keys

@[simp]
def support_zero : (0 : DSortedFinsupp σ R cmp).support = ∅ := rfl

lemma support_pairwise (l : DSortedFinsupp σ R cmp) : l.support.Pairwise (cmp · · = .lt) :=
  List.pairwise_map.mpr l.pairwise

lemma mem_support_iff [DecidableEq σ] (l : DSortedFinsupp σ R cmp) (a : σ) :
    a ∈ l.support ↔ l a ≠ 0 := by
  simp [apply_eq_zero_iff_not_mem_val_keys, support]

-- lemma toFinset_support [DecidableEq σ] (l : DSortedFinsupp σ R cmp) :
--     l.support.toFinset = Function.support l := by
--   ext x
--   simp [support, apply_ne_zero_iff]

-- lemma support_finite [DecidableEq σ] (l : DSortedFinsupp σ R cmp) :
--     (Function.support l).Finite := by simp [← toFinset_support]

end Basic

section DFinsupp

-- instance : IsAntisymm (α := σ) (cmp · · |>.isLE) where
--   antisymm _ _ h h' := Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h h')

-- instance : IsAntisymm (α := σ) (cmp · · ≠ .gt) := by
--   simp [Ordering.ne_gt_iff_isLE]
--   exact inferInstance

-- instance : IsTrans (α := σ) (cmp · · |>.isLE) where
--   trans _ _ _ := Std.TransCmp.isLE_trans

-- instance : IsTrans (α := σ) (cmp · · ≠ .gt) := by
--   simp [Ordering.ne_gt_iff_isLE]
--   exact inferInstance

-- instance : IsTotal (α := σ) (cmp · · |>.isLE) where
--   total a b := by
--     rw [or_iff_not_imp_left]
--     intro h
--     simp [Std.OrientedCmp.lt_of_not_isLE h]

-- instance : IsTotal (α := σ) (cmp · · ≠ .gt) := by
--   simp [Ordering.ne_gt_iff_isLE]
--   exact inferInstance

-- variable (cmp) in
-- def linearOrder [DecidableRel (cmp · · |>.isLE)] : LinearOrder σ where
--   le := (cmp · · |>.isLE)
--   le_refl _ := Std.ReflCmp.isLE_rfl
--   le_trans _ _ _ a b := Std.TransCmp.isLE_trans a b
--   le_antisymm _ _ h h' := Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h h')
--   le_total := (inferInstanceAs <| IsTotal (α := σ) (cmp · · |>.isLE)).total
--   toDecidableLE := inferInstance

variable (cmp) in
def onSupport (f : (k : σ) → R k) (s : Finset σ) (h : ∀ x, x ∈ s ↔ f x ≠ 0) :
    DSortedFinsupp σ R cmp :=
  .mk' (DSortedListMap.onFinset cmp (some <| f ·) s) (by simp [DSortedListMap.get?_onFinset, ← h])

@[simp]
def apply_onSupport [DecidableEq σ] {f : (k : σ) → R k} {s} (h : ∀ x, x ∈ s ↔ f x ≠ 0) :
    onSupport cmp f s h = f := by
  funext x
  specialize h x
  simp [onSupport, DSortedListMap.get?_onFinset, mk', apply_def]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx] at *
    simp [h]

def equivDFinsupp [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)] :
    Equiv (DSortedFinsupp σ R cmp) (Π₀ k : σ, R k) where
  toFun l := DFinsupp.mk l.support.toFinset (l ·.val)
  invFun f := onSupport cmp f f.support (fun _ ↦ f.mem_support_iff)
  left_inv l := by ext x; simp [apply_onSupport, mem_support_iff]; simp_intro ..
  right_inv f := by ext x; simp [apply_onSupport, mem_support_iff]; simp_intro ..

lemma equivDFinsupp_coe [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)]
    (l : DSortedFinsupp σ R cmp) :
    Eq (α := (k : σ) → R k) (equivDFinsupp l) l := by
  ext x
  simp [equivDFinsupp, mem_support_iff]
  simp_intro ..

lemma equivDFinsupp_symm_coe [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)]
    (f : Π₀ k : σ, R k) :
    Eq (α := (k : σ) → R k) (equivDFinsupp (cmp := cmp) |>.symm f) f := by
  simp [equivDFinsupp, apply_onSupport]

lemma equivDFinsupp_coe_zero [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)] :
    equivDFinsupp (0 : DSortedFinsupp σ R cmp) = 0 := rfl

lemma equivDFinsupp_symm_coe_zero [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)] :
    (equivDFinsupp.symm 0) = (0 : DSortedFinsupp σ R cmp) := by
  ext x
  simp [equivDFinsupp, apply_onSupport]

@[simp]
def equivDFinsupp_apply [DecidableEq σ] [∀ k, ∀ b : R k, Decidable (b = 0)] (x : σ)
    (l : DSortedFinsupp σ R cmp) :
    l.equivDFinsupp x = l x := by
  simp [equivDFinsupp, mem_support_iff]
  simp_intro _

end DFinsupp

section mergwWith

variable [∀ k : σ, ∀ a : R k, Decidable (a = 0)]
variable (mergeFn : (k : σ) → R k → R k → R k)
variable (l₁ l₂ : DSortedFinsupp σ R cmp)

#check Finsupp.zipWith_apply

def mergeWith : DSortedFinsupp σ R cmp :=
  ⟨l₁.val.mergeWith (let a := mergeFn · · ·; if a = 0 then none else some a) l₂.val,
    by
      classical
      intro a ha
      simp [← DSortedListMap.get?_eq_some_iff_mem_val, DSortedListMap.mergeWith_get?] at ha
      split at ha
      · expose_names
        simp at ha
        apply ne_zero_of_val_get?_eq_some at heq
        rwa [ha] at heq
      · expose_names
        simp at ha
        apply ne_zero_of_val_get?_eq_some at heq_1
        rwa [ha] at heq_1
      · expose_names
        intro ha'
        simp [ha'] at ha
      · simp at ha
  ⟩

@[simp]
lemma mergeWith_apply [DecidableEq σ] (a : σ)
    (hzero : ∀ b : R a, mergeFn a b 0 = b)
    (hzero' : ∀ b : R a, mergeFn a 0 b = b) :
    (l₁.mergeWith mergeFn l₂ a) = mergeFn a (l₁ a) (l₂ a) := by
  simp [mergeWith]
  nth_rw 1 [apply_def, DSortedListMap.mergeWith_get?]
  split
  · expose_names
    rw [← apply_eq_zero_iff_val_get?_eq_none] at heq_1
    apply apply_eq_of_get?_val_eq_some at heq
    simp [heq_1, heq, hzero]
  · expose_names
    rw [← apply_eq_zero_iff_val_get?_eq_none] at heq
    apply apply_eq_of_get?_val_eq_some at heq_1
    simp [heq_1, heq, hzero']
  · expose_names
    simp [get?_val_eq_some_iff] at heq heq_1
    rw [heq.1, heq_1.1]
    split_ifs with h
    · simp [h]
    · simp
  · rw [← apply_eq_zero_iff_val_get?_eq_none] at *
    simp [*]

end mergwWith

section Add

variable {R : σ → Type*} [∀ k : σ, AddZeroClass (R k)] [∀ k : σ, ∀ a : R k, Decidable (a = 0)]

instance : Fact <| ∀ a : σ, ∀ b : R a, b + 0 = b ∧ 0 + b = b := ⟨by simp⟩

instance : Add (DSortedFinsupp σ R cmp) where
  add l₁ l₂ := l₁.mergeWith (fun _ ↦ HAdd.hAdd) l₂

lemma add_def (l₁ l₂ : DSortedFinsupp σ R cmp) :
    l₁ + l₂ = l₁.mergeWith (fun _ ↦ HAdd.hAdd) l₂ := rfl

@[simp]
lemma add_apply [DecidableEq σ] (l₁ l₂ : DSortedFinsupp σ R cmp) (x : σ) :
    (l₁ + l₂) x = l₁ x + l₂ x := by
  simp [add_def]

def addEquivDFinsupp [DecidableEq σ] : DSortedFinsupp σ R cmp ≃+ (Π₀ k : σ, R k) :=
{ equivDFinsupp (σ := σ) (R := R) (cmp := cmp) with
  map_add' l₁ l₂ := by
    ext x
    simp [equivDFinsupp_coe, add_apply]
}

private def example2 : DSortedFinsupp Int (fun _ ↦ Int) compare :=
  ⟨show DSortedListMap Int (fun _ ↦ Int) compare from ⟨[⟨1, 5⟩, ⟨3, 4⟩], by decide⟩, by decide⟩

#reduce example1 + example2

end Add

section mapRange

variable {R' : σ → Type*} [∀ k : σ, Zero (R' k)] (f : (k : σ) → R k → R' k)
  [∀ i : σ, ∀ x : R i, Decidable (f i x = 0)]

set_option linter.unusedVariables false in
def mapRange (hf : ∀ i, f i 0 = 0) (l : DSortedFinsupp σ R cmp) :
    DSortedFinsupp σ R' cmp :=
  mk' (l.val.filterMap (let r := f · ·; if r = 0 then none else some r)) (by
    simp_intro a [DSortedListMap.filterMap_get?, Option.bind]
    split
    · simp
    · simp
  )

@[simp]
lemma mapRange_apply [DecidableEq σ] (hf : ∀ i, f i 0 = 0) (l : DSortedFinsupp σ R cmp) (x : σ) :
    l.mapRange f hf x = f x (l x) := by
  simp [mapRange, mk', apply_def]
  simp [DSortedListMap.filterMap_get?, Option.bind]
  split
  · simp [*]
  · simp
    split_ifs
    · simp [*]
    · simp [*]

end mapRange

section SumProd

variable {N : Type*} [CommMonoid N] [DecidableEq σ]

@[to_additive]
def prod [∀ i : σ, DecidableEq (R i)] (l : DSortedFinsupp σ R cmp)
    (g : (k : σ) → R k → N) : N :=
  ∏ a ∈ l.val.val.toFinset, g a.1 a.2

@[simp]
theorem _root_.List.toFinset_map {α β} [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s : List α) :
    (s.map f).toFinset = s.toFinset.map f := by
  simp [← Finset.coe_inj]
  ext x
  simp

@[simp]
theorem _root_.List.coe_toFinset_map {α β} [DecidableEq α] [DecidableEq β] {f : α → β}
    (s : List α) :
    (s.map f).toFinset = f '' s.toFinset := by
  ext x
  simp

@[to_additive]
def prod_eq_prod_support [∀ i : σ, DecidableEq (R i)]
    (l : DSortedFinsupp σ R cmp) (g : (k : σ) → R k → N) :
    l.prod g = ∏ a ∈ l.support.toFinset, g a (l a) := by
  unfold prod
  have := Finset.prod_map l.support.toFinset
    (⟨fun x ↦ show Sigma R from ⟨x, l x⟩, by simp [Function.Injective]⟩)
    (fun a ↦ g a.1 a.2)
  convert this
  · classical
    ext x
    simp [apply_def]
    simp [support, DSortedListMap.mem_keys_iff, ← DSortedListMap.get?_eq_some_iff_mem_val]
    constructor
    · intro h
      use x.1
      simp [h]
    · rintro ⟨x', h1, h2⟩
      rw [Sigma.eq_of_eq (show x.1 = x' by aesop)]
      simp [Option.ne_none_iff_exists] at h1
      obtain ⟨x'', h1⟩ := h1
      simp [← h1] at h2
      simp [← h1]
      aesop

end SumProd
