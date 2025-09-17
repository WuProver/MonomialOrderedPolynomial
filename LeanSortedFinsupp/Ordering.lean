import Std
import Mathlib

instance {α} {cmp : α → α → Ordering} [Std.ReflCmp cmp] :
    Std.ReflCmp (cmp · · |>.swap) where
  compare_self := by simp [Std.ReflCmp.compare_self]

instance {α} {cmp : α → α → Ordering} [Std.LawfulEqCmp cmp] :
    Std.LawfulEqCmp (cmp · · |>.swap) where
  eq_of_compare := by simp

instance {α} {cmp : α → α → Ordering} [Std.OrientedCmp cmp] :
    Std.OrientedCmp (cmp · · |>.swap) where
  eq_swap := by simp [← Std.OrientedCmp.eq_swap]

instance {α} {cmp : α → α → Ordering} [Std.TransCmp cmp] :
    Std.TransCmp (cmp · · |>.swap) where
  isLE_trans := by
    intro _ _ _
    simp
    exact Std.TransCmp.isGE_trans

#check AddLeftStrictMono

instance {G} {cmp : G → G → Ordering} [Add G] [LinearOrder G]
    [AddLeftStrictMono G] [Std.LawfulCmp cmp] :
    Fact <| ∀ (a i j : G), cmp i j = cmp (a + i) (a + j) where
  out a i j := by
    rcases h : cmp i j
    · rw [Std.LawfulCmp.eq_lt_iff_lt] at h
      rw [eq_comm, Std.LawfulCmp.eq_lt_iff_lt (cmp := cmp)]
      exact add_lt_add_left h a
    · simp at h
      rw [eq_comm, h]
      simp
    · rw [eq_comm, Std.LawfulLTCmp.eq_gt_iff_gt]
      rw [Std.LawfulLTCmp.eq_gt_iff_gt] at h
      exact add_lt_add_left h a

instance {G} {cmp : G → G → Ordering} [Add G]
    [fact : Fact <| ∀ (a i j : G), cmp i j = cmp (a + i) (a + j)] :
    Fact <| ∀ (a i j : G), (cmp i j).swap = (cmp (a + i) (a + j)).swap where
  out := by
    simp
    exact fact.elim

def PartialOrder.ofLawfulCmp {R : Type*} (cmp : R → R → Ordering) [LT R] [LE R]
    [Std.LawfulCmp cmp] :
    PartialOrder R where
  le_refl := by simp [← Std.LawfulLECmp.isLE_iff_le (cmp := cmp), Std.ReflCmp.isLE_rfl]
  le_trans a b c := by
    simp [← Std.LawfulLECmp.isLE_iff_le (cmp := cmp)]
    exact Std.TransCmp.isLE_trans
  le_antisymm a b h := by
    rw [← Std.LawfulLECmp.isLE_iff_le (cmp := cmp),
      ← Std.LawfulEqCmp.compare_eq_iff_eq (cmp := cmp)]
    apply Std.OrientedCmp.isLE_antisymm
    rwa [Std.LawfulCmp.isLE_iff_le (cmp := cmp)]
  lt_iff_le_not_ge a b := by
    simp [← Std.LawfulLECmp.isLE_iff_le (cmp := cmp), ← Std.LawfulLTCmp.eq_lt_iff_lt (cmp := cmp),
      Std.OrientedCmp.gt_iff_lt]
    simp_intro ..

def PartialOrder.ofLawfulOrd {R : Type*} [LT R] [LE R] [Ord R]
    [Std.LawfulOrd R] : PartialOrder R :=
  PartialOrder.ofLawfulCmp compare

-- open Classical in
def LinearOrder.ofLawfulCmp {R : Type*} (cmp : R → R → Ordering) [LT R] [LE R]
    [inst : Std.LawfulCmp cmp]
    -- `_ : cmp = cmp := rfl` is a workaround to "mention" `cmp` in its type
    (instDecidableLE : ∀ (_ : cmp = cmp := rfl), DecidableLE R := by
      first |
        exact fun _ ↦ inferInstance |
          letI cmp' : R → R → Ordering := ?cmp
          convert_to ∀ (_ : cmp' = cmp'), _
          exact fun (_ : cmp' = cmp') ↦
            fun a b ↦ decidable_of_iff ((cmp' a b).isLE = true) Std.LawfulCmp.isLE_iff_le
    )
    (instDecidableLT : ∀ (_ : cmp = cmp := rfl), DecidableLT R := by
      first |
        exact inferInstance |
          letI cmp' : R → R → Ordering := ?cmp
          convert_to ∀ (_ : cmp' = cmp'), _
          exact fun (_ : cmp' = cmp') ↦
            fun a b ↦ decidable_of_iff (cmp' a b = .lt) Std.LawfulCmp.eq_lt_iff_lt)
    (instDecidableEq : ∀ (_ : cmp = cmp := rfl), DecidableEq R := by
      first |
        exact inferInstance |
          letI cmp' : R → R → Ordering := ?cmp
          convert_to ∀ (_ : cmp' = cmp'), _
          exact fun (_ : cmp' = cmp') ↦
            fun a b ↦ decidable_of_iff (cmp' a b = .eq) Std.LawfulEqCmp.compare_eq_iff_eq) :
    LinearOrder R := {
  PartialOrder.ofLawfulCmp cmp with
  le_total a b := by
    simp [← Std.LawfulCmp.isLE_iff_le (cmp := cmp),
      ← Std.OrientedCmp.isGE_iff_isLE (a := a)]
    rcases cmp a b <;> simp
  toDecidableLE := instDecidableLE
  toDecidableEq := instDecidableEq
  toDecidableLT := instDecidableLT
  -- toDecidableLE := by
  --   exact fun a b ↦ decidable_of_iff ((cmp a b).isLE = true) Std.LawfulCmp.isLE_iff_le
  -- toDecidableLT := by
  --   exact fun a b ↦ decidable_of_iff (cmp a b = .lt) Std.LawfulCmp.eq_lt_iff_lt
  -- toDecidableEq := by
  --   exact fun a b ↦ decidable_of_iff (cmp a b = .eq) Std.LawfulEqCmp.compare_eq_iff_eq
  -- compare_eq_compareOfLessAndEq a b := by
  --   simp_rw [compareOfLessAndEq,
  --     ← Std.LawfulCmp.eq_lt_iff_lt (cmp := compare),
  --     ← Std.LawfulEqCmp.compare_eq_iff_eq (α := R) (cmp := compare)
  --   ]
  --   split_ifs with h h'
  --   · exact h
  --   · exact h'
  --   · cases h'' : compare a b
  --     · simp [h''] at h
  --     · simp [h''] at h'
  --     · rfl
}

def LinearOrder.ofLawfulOrd {R : Type*} [LT R] [LE R] [Ord R]
    [Std.LawfulOrd R]
    (instDecidableLE : DecidableLE R := by
      first |
        exact fun _ ↦ inferInstance |
        exact fun a b ↦ decidable_of_iff ((compare a b).isLE = true) Std.LawfulCmp.isLE_iff_le)
    (instDecidableLT : DecidableLT R := by
      first |
        exact inferInstance |
        exact fun  a b ↦ decidable_of_iff (compare a b = .lt) Std.LawfulCmp.eq_lt_iff_lt)
    (instDecidableEq : DecidableEq R := by
      first |
        exact inferInstance |
        exact fun  a b ↦ decidable_of_iff (compare a b = .eq) Std.LawfulEqCmp.compare_eq_iff_eq) :
    LinearOrder R := by
  exact LinearOrder.ofLawfulCmp compare
    (instDecidableLE := fun _ ↦ instDecidableLE) (instDecidableLT := fun _ ↦ instDecidableLT)
    (instDecidableEq := fun _ ↦ instDecidableEq)

instance (priority := low) LinearOrder.toLawfulOrd {R : Type*} [LinearOrder R] : Std.LawfulOrd R :=
  {}

set_option trace.Meta.synthInstance true
#synth LinearOrder Rat
#synth Std.LawfulOrd Rat
