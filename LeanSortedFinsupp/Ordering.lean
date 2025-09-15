import Std

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
