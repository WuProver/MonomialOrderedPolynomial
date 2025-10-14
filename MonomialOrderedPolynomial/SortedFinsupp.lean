import MonomialOrderedPolynomial.DSortedFinsupp

/-!

# function `SortedFinsupp σ R` with finite support, based on sorted list

For more information, refer to `DSortedFinsupp`.

## Definitions

- `SortedFinsupp.equivFinsupp`: the equivalence between `SortedFinsupp σ R` and `Finsupp σ R`,
  where application is preserved, i.e. for `l : SortedFinsupp σ R`, `(equivFinsupp l) x = l x`,
  or `⇑(equivFinsupp l) = ⇑l`.

For others, refer to definitions of `DSortedFinsupp`.

## TODO

Refactor it into structure without `Sigma`, which uses dependent type on the value and visibly
reduce performance in kernel.

-/

/--
function with finite support, based on `DSortedFinsupp`.
-/
def SortedFinsupp σ R
    [Zero R] (cmp : σ → σ → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :=
  DSortedFinsupp σ (fun _ ↦ R) cmp

namespace SortedFinsupp

variable {σ : Type*} {cmp : σ → σ → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Finsupp

variable {R : Type*} [Zero R]

instance [DecidableEq σ] [DecidableEq R] : DecidableEq (SortedFinsupp σ R cmp) :=
  inferInstanceAs <| DecidableEq <| DSortedFinsupp σ (fun _ ↦ R) cmp

instance : Zero (SortedFinsupp σ R cmp) :=
  inferInstanceAs <| Zero <| DSortedFinsupp σ (fun _ ↦ R) cmp

@[inline]
instance instFunLike [DecidableEq σ] : FunLike (SortedFinsupp σ R cmp) σ R :=
  inferInstanceAs <| FunLike (DSortedFinsupp σ (fun _ ↦ R) cmp) σ R

lemma ext_iff [DecidableEq σ] {l1 l2 : SortedFinsupp σ R cmp} :
    l1 = l2 ↔ ∀ s : σ, l1 s = l2 s := DSortedFinsupp.ext_iff

@[ext]
lemma ext [DecidableEq σ] {l1 l2 : SortedFinsupp σ R cmp} (h : ∀ s : σ, l1 s = l2 s) :
    l1 = l2 := ext_iff.mpr h

@[simp]
lemma zero_apply [DecidableEq σ] (x : σ) : (0 : SortedFinsupp σ R cmp) x = 0 := rfl

@[simp]
lemma coe_zero  [DecidableEq σ] : ⇑(0 : SortedFinsupp σ R cmp) = 0 := rfl

variable (cmp) in
@[inherit_doc DSortedFinsupp.single]
def single (x : σ) (y : R) [Decidable (y = 0)] : SortedFinsupp σ R cmp :=
  DSortedFinsupp.single cmp x y

@[simp]
lemma single_apply [DecidableEq σ] (a : σ) (b : R) [Decidable (b = 0)] (c : σ) :
    (single cmp a b) c = if a = c then b else 0 := by
  simp [single]
  -- why `simp [DSortedFinsupp.single_apply]` doesn't work???
  rw [DSortedFinsupp.single_apply]
  simp

lemma eq_zero_iff_apply_eq_zero [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    l = 0 ↔ ∀ x : σ, l x = 0 := DSortedFinsupp.eq_zero_iff_apply_eq_zero l

private def example1 : SortedFinsupp Int Int compare := ⟨⟨[⟨1, 3⟩, ⟨2, 4⟩], by decide⟩, by decide⟩

#reduce ((example1 : Int → Int) 2) + 2

#reduce example1 1

#reduce example1 3

@[inherit_doc DSortedFinsupp.support]
def support (l : SortedFinsupp σ R cmp) : List σ := DSortedFinsupp.support l

@[simp]
def support_zero : (0 : SortedFinsupp σ R cmp).support = ∅ := rfl

lemma support_pairwise (l : SortedFinsupp σ R cmp) : l.support.Pairwise (cmp · · = .lt) :=
  List.pairwise_map.mpr l.pairwise

lemma mem_support_iff [DecidableEq σ] (l : SortedFinsupp σ R cmp) (a : σ) :
    a ∈ l.support ↔ l a ≠ 0 := DSortedFinsupp.mem_support_iff ..

lemma toFinset_support [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    l.support.toFinset = Function.support l := by
  ext x
  simp [mem_support_iff]

-- todo: should be generalized to DSortedFinsupp
@[simp]
def single_support (a : σ) (b : R) [Decidable (b = 0)] :
    (single cmp a b).support = if b = 0 then [] else [a] := by
  classical
  split_ifs
  · simpa [List.eq_nil_iff_forall_not_mem, mem_support_iff]
  · -- ugly....
    unfold single support DSortedFinsupp.single
    simp [*]
    rfl

lemma support_finite [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    (Function.support l).Finite := by simp [← toFinset_support]

variable (cmp) in
def onSupport (f : σ → R) (s : Finset σ)
    (h : ∀ x, x ∈ s ↔ f x ≠ 0) :
    SortedFinsupp σ R cmp := DSortedFinsupp.onSupport cmp f s h

@[simp]
def apply_onSupport [DecidableEq σ] {f : σ → R} {s h} :
    onSupport cmp f s h = f := DSortedFinsupp.apply_onSupport h

def equivDFinsupp [DecidableEq σ] [∀ y : R, Decidable (y = 0)] :
    Equiv (SortedFinsupp σ R cmp) (Π₀ _ : σ, R) :=
  DSortedFinsupp.equivDFinsupp

def equivDFinsupp_apply [DecidableEq σ] [∀ y : R, Decidable (y = 0)]
    (x : σ) (l : SortedFinsupp σ R cmp) :
    l.equivDFinsupp x = l x := DSortedFinsupp.equivDFinsupp_apply ..

def equivFinsupp [DecidableEq σ] :
    Equiv (SortedFinsupp σ R cmp) (σ →₀ R) where
  toFun l := Finsupp.mk l.support.toFinset l (by simp [l.mem_support_iff])
  invFun f := onSupport cmp f f.support (fun _ ↦ f.mem_support_iff)
  left_inv l := by ext x; simp [apply_onSupport]
  right_inv f := by ext x; simp [apply_onSupport]

lemma equivFinsupp_coe [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    Eq (α := σ → R) (equivFinsupp l) l := rfl

lemma equivFinsupp_symm_coe [DecidableEq σ] (f : σ →₀ R) :
    Eq (α := σ → R) (equivFinsupp (cmp := cmp) |>.symm f) f := by
  simp [equivFinsupp, apply_onSupport]

lemma equivFinsupp_coe_zero [DecidableEq σ] :
    equivFinsupp (0 : SortedFinsupp σ R cmp) = 0 := rfl

lemma equivFinsupp_symm_coe_zero [DecidableEq σ] :
    (equivFinsupp.symm (0 : σ →₀ R)) = (0 : SortedFinsupp σ R cmp) := by
  ext x
  simp [equivFinsupp, apply_onSupport]

@[simp]
lemma equivFinsupp_apply [DecidableEq σ] (x : σ) (l : SortedFinsupp σ R cmp) :
    l.equivFinsupp x = l x := by
  simp [equivFinsupp]

variable (cmp) in
lemma equivFinsupp_symm_apply [DecidableEq σ] (x : σ) (l : σ →₀ R) :
    (equivFinsupp (cmp := cmp)).symm l x = l x := by
  simp [equivFinsupp, apply_onSupport]

lemma support_eq_equivFinsupp_support [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    l.support.toFinset = (equivFinsupp l).support := by
  ext x
  simp [mem_support_iff]

@[simp]
lemma equivFinsupp_zero [DecidableEq σ] :
    equivFinsupp (0 : SortedFinsupp σ R cmp) = 0 := rfl

@[simp]
lemma equivFinsupp_single [DecidableEq σ] (a : σ) (b : R) [Decidable (b = 0)] :
    equivFinsupp (single cmp a b) = Finsupp.single a b := by
  ext x
  simp [Finsupp.single_apply]

end Finsupp

section mergeWith

variable {R : Type*} [Zero R] [∀ a : R, Decidable (a = 0)]
variable (mergeFn : (k : σ) → R → R → R)
variable (l₁ l₂ : SortedFinsupp σ R cmp)

@[inherit_doc DSortedFinsupp.mergeWith]
def mergeWith : SortedFinsupp σ R cmp := DSortedFinsupp.mergeWith mergeFn l₁ l₂

@[simp]
lemma mergeWith_apply [DecidableEq σ] (a : σ)
    (hzero : ∀ b : R, mergeFn a b 0 = b)
    (hzero' : ∀ b : R, mergeFn a 0 b = b) :
    (l₁.mergeWith mergeFn l₂) a = mergeFn a (l₁ a) (l₂ a) :=
  DSortedFinsupp.mergeWith_apply mergeFn l₁ l₂ a hzero hzero'

variable (mergeFn : R → R → R) in
lemma mergeWith_eq_equivFinsupp_zipWith [DecidableEq σ] (a : σ)
    (hzero : ∀ b : R, mergeFn b 0 = b)
    (hzero' : ∀ b : R, mergeFn 0 b = b) :
    l₁.mergeWith (fun _ ↦ mergeFn) l₂ a =
      (equivFinsupp l₁).zipWith mergeFn (hzero 0) (equivFinsupp l₂) a := by
  classical
  simp [Finsupp.zipWith_apply, mergeWith_apply (fun _ ↦ mergeFn) l₁ l₂ a hzero hzero']

#check Finsupp.zipWith

end mergeWith

section Add

variable {R : Type*} [AddZeroClass R] [∀ a : R, Decidable (a = 0)]

instance instAdd : Add (SortedFinsupp σ R cmp) := DSortedFinsupp.instAdd

@[simp]
lemma add_apply [DecidableEq σ] (l₁ l₂ : SortedFinsupp σ R cmp) (x : σ) :
    (l₁ + l₂) x = l₁ x + l₂ x := DSortedFinsupp.add_apply ..

@[simp]
lemma coe_add [DecidableEq σ] (l₁ l₂ : SortedFinsupp σ R cmp) :
    ⇑(l₁ + l₂) = ⇑l₁ + ⇑l₂ := by
  ext
  exact add_apply ..

def addEquivDFinsupp [DecidableEq σ] : SortedFinsupp σ R cmp ≃+ (Π₀ _ : σ, R) :=
  DSortedFinsupp.addEquivDFinsupp

def addEquivFinsupp [DecidableEq σ] : SortedFinsupp σ R cmp ≃+ (σ →₀ R) :=
{ equivFinsupp with
  map_add' l₁ l₂ := by
    ext x
    simp [equivFinsupp_coe, add_apply]}

instance instAddZeroClass [DecidableEq σ] : AddZeroClass (SortedFinsupp σ R cmp) :=
  fast_instance% DFunLike.coe_injective.addZeroClass _ (by ext; simp) (by intro _ _; ext; simp)

#check AddMonoidAlgebra.singleAddHom
def singleAddHom [DecidableEq σ] [∀ i : R, Decidable (i = 0)] (x : σ) :
    R →+ SortedFinsupp σ R cmp where
  toFun y := single cmp x y
  map_add' := by
    intro _ _
    ext
    simp
    aesop
  map_zero' := by
    ext
    simp

private def example2 : SortedFinsupp Int Int compare := ⟨⟨[⟨1, 5⟩, ⟨3, 4⟩], by decide⟩, by decide⟩

#reduce example1 + example2

end Add

section mapRange

variable {β₁ β₂ : Type*} [Zero β₁] [Zero β₂]

#check Finsupp.mapRange_apply

@[inherit_doc DSortedFinsupp.mapRange]
def mapRange (f : σ → β₁ → β₂) (hf : ∀ i, f i 0 = 0)
    [∀ i : σ, ∀ x : β₁, Decidable (f i x = 0)] (l : SortedFinsupp σ β₁ cmp) :
    SortedFinsupp σ β₂ cmp := DSortedFinsupp.mapRange f hf l

@[simp]
def mapRange_apply [DecidableEq σ] {f : σ → β₁ → β₂} (hf : ∀ i, f i 0 = 0)
    [∀ i : σ, ∀ x : β₁, Decidable (f i x = 0)] (l : SortedFinsupp σ β₁ cmp) (x : σ) :
    l.mapRange f hf x = f x (l x) := DSortedFinsupp.mapRange_apply ..

end mapRange

section Sub

variable [DecidableEq σ] {R : Type*} [AddCommMonoid R] [PartialOrder R]
  [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R] [(a : R) → Decidable (a = 0)]

-- inefficient -- the worst time complexit to compute `a - b` is $O(length of a * length of b)$.
-- todo: optimize.
instance tsub : Sub (SortedFinsupp σ R cmp) where
  sub a b :=
    a.mapRange (fun i m => m - b i) (by simp)

lemma tsub_apply (l₁ l₂ : SortedFinsupp σ R cmp) (a : σ) :
    (l₁ - l₂) a = l₁ a - l₂ a := by
  convert_to (l₁.mapRange _ _) a = _
  rw [mapRange_apply]

end Sub

section mapDomain

#check Finsupp.mapDomain

end mapDomain

section SMul

variable {R M} [Zero R] [Zero M] [SMulWithZero R M] [∀ y : M, Decidable (y = 0)]

instance instSMulWithZero :
    SMulWithZero R (SortedFinsupp σ M cmp) where
  smul s l := l.mapRange (fun _ ↦ (s • ·)) (by simp)
  smul_zero s := by
    classical
    convert_to (0 : SortedFinsupp σ M cmp).mapRange (fun _ ↦ (s • ·)) (by simp) = 0
    ext x
    simp
  zero_smul l := by
    convert_to l.mapRange (fun _ ↦ ((0 : R) • ·)) (by simp) = 0
    classical
    ext x
    simp

lemma smul_def (s : R) (l : SortedFinsupp σ M cmp) :
    s • l = l.mapRange (fun _ ↦ (s • ·)) (by simp) := rfl

@[simp]
lemma smul_apply [DecidableEq σ] (s : R) (l : SortedFinsupp σ M cmp) (x : σ) :
    (s • l) x = s • (l x) := by
  simp [smul_def]

end SMul

section AddMonoid

variable {R} [AddMonoid R] [∀ a : R, Decidable (a = 0)]

instance instNatSMul : SMul ℕ (SortedFinsupp σ R cmp) where
  smul n v := v.mapRange (fun _ ↦ (n • ·)) (fun _ ↦ nsmul_zero _)

lemma nat_smul_def (n : ℕ) (l : SortedFinsupp σ R cmp) :
    n • l = l.mapRange (fun _ ↦ (n • ·)) (fun _ ↦ nsmul_zero _) := rfl

lemma nat_smul_apply [DecidableEq σ] (n : ℕ) (x : σ) (l : SortedFinsupp σ R cmp) :
    (n • l) x = n • (l x) := by
  simp [nat_smul_def]

lemma coe_nat_smul [DecidableEq σ] (n : ℕ) (l : SortedFinsupp σ R cmp) :
    ⇑(n • l) = n • ⇑l := by
  ext
  exact nat_smul_apply ..

instance instAddMonoid [DecidableEq σ] : AddMonoid (SortedFinsupp σ R cmp) :=
  fast_instance% DFunLike.coe_injective.addMonoid _ coe_zero coe_add (by simp [coe_nat_smul])

end AddMonoid

section AddCommMonoid

variable {R} [AddCommMonoid R] [∀ a : R, Decidable (a = 0)]

instance instAddCommMonoid [DecidableEq σ] : AddCommMonoid (SortedFinsupp σ R cmp) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (by simp [coe_nat_smul])

end AddCommMonoid

section SumProd

variable {N R : Type*} [CommMonoid N] [DecidableEq σ] [Zero R] [DecidableEq R]

@[to_additive]
def prod (l : SortedFinsupp σ R cmp)
    (g : σ → R → N) : N := DSortedFinsupp.prod l g

@[to_additive]
def prod_eq_prod_support
    (l : SortedFinsupp σ R cmp) (g : σ → R → N) :
    l.prod g = ∏ a ∈ l.support.toFinset, g a (l a) := DSortedFinsupp.prod_eq_prod_support ..

@[to_additive]
def prod_eq_equivFinsupp_prod (l : SortedFinsupp σ R cmp) (g : σ → R → N) :
    l.prod g = (equivFinsupp l).prod g := by
  simp [prod_eq_prod_support, support_eq_equivFinsupp_support, Finsupp.prod]

-- todo: should be generalized later
@[to_additive (attr := simp)]
def single_prod (g : σ → R → N)
    (hg : ∀ i : σ, g i 0 = 1)
    (a : σ) (b : R) :
    (single cmp a b).prod g = g a b := by
  classical
  simp [prod_eq_prod_support, single_support]
  split_ifs
  · simp [*]
  · simp

#check single_sum

-- todo: should be generalized to `DSortedFinsupp` later
@[simp]
lemma zero_sum {R' : Type*} [AddCommMonoid R'] (g : σ → R → R') :
    (0 : SortedFinsupp σ R cmp).sum g = 0 := rfl

-- todo: should be generalized to `DSortedFinsupp` later
@[simp]
lemma sum_zero {R' : Type*} [AddCommMonoid R']
    (l : SortedFinsupp σ R cmp) :
    l.sum (fun _ _ ↦ 0) = (0 : R') := by
  simp [sum, DSortedFinsupp.sum]

-- todo: should be generalized to `DSortedFinsupp` later
@[to_additive (attr := simp)]
lemma prod_apply
    {R' R'' : Type*} [CommMonoid R'] [CommMonoid R'']
    (l : SortedFinsupp σ R cmp) (g : σ → R → R')
    {F} [FunLike F R' R''] [MonoidHomClass F R' R''] (f : F) :
    f (l.prod g) = l.prod (f <| g · ·) := by
  simp [prod_eq_prod_support]

variable (cmp) in
def addMonoidHom (R) [AddCommMonoid R] [(a : R) → Decidable (a = 0)]
    (x : σ) :
    AddMonoidHom (SortedFinsupp σ R cmp) R where
  toFun l := l x
  map_zero' := by simp
  map_add' := by simp

-- todo: should be generalized to DSortedFinsupp later
-- `DecidableEq R'` can be generalized to `∀ a : R', Decidable (a = 0)`
@[simp]
lemma sum_apply'
    {σ' : Type*} {cmp' : σ' → σ' → Ordering} [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    {R' : Type*} [AddCommMonoid R'] [DecidableEq σ'] [DecidableEq R']
    (l : SortedFinsupp σ R cmp)
    (g : σ → R → SortedFinsupp σ' R' cmp') (x : σ') :
    (l.sum g) x = l.sum (g · · x) :=
  sum_apply (f := addMonoidHom cmp' R' x) ..

#check Finsupp.mapRange_apply
-- todo: should be generalized later
@[simp]
lemma mapRange_sum
    {R' : Type*} [Zero R']
    {R'' : Type*} [AddCommMonoid R''] [DecidableEq R']
    (f : σ → R → R') (hf : ∀ i, f i 0 = 0)
    (g : σ → R' → R'') (hg : ∀ i, g i 0 = 0)
    (l : SortedFinsupp σ R cmp) :
    (l.mapRange f hf).sum g = l.sum (fun x ↦ (g x <| f x ·)) := by
  classical
  simp [sum_eq_sum_support, mapRange_apply hf]
  -- sorry
  have : (mapRange f hf l).support.toFinset = l.support.toFinset.filter (fun x ↦ f x (l x) ≠ 0) := by
      ext x
      simp [mem_support_iff, mapRange_apply hf, Finset.mem_filter]
      intro h
      by_contra hg
      rw [hg] at h
      exact h (hf x)
  simp [this]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  simp [mem_support_iff] at hx
  simp
  intro h
  rw [h]
  simp [hg]

end SumProd

section mapDomain

variable {σ' R} [Zero R] {cmp' : σ' → σ' → Ordering} [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
variable (f : σ → σ') (hf : ∀ i j, cmp i j = cmp' (f i) (f j))

-- todo: we should generalize it later
def mapDomain (l : SortedFinsupp σ R cmp) :
    SortedFinsupp σ' R cmp' :=
  ⟨
    ⟨l.val.val.map (fun a ↦ ⟨f a.1, a.2⟩),
      by
        rw [List.chain'_iff_pairwise, List.pairwise_map]
        simp [← hf, ← List.chain'_iff_pairwise]
        exact l.val.2⟩,
    (by
      have := l.2
      simp at this
      simp
      intro a x x1 hx ha
      aesop)
  ⟩

@[simp]
lemma mapDomain_apply [DecidableEq σ] [DecidableEq σ'] (x : σ) (l : SortedFinsupp σ R cmp) :
    l.mapDomain f hf (f x) = l x := by
  have : Function.Injective f := by
    intro a b h
    have := hf a b
    rw [h] at this
    have ha : cmp' (f b) (f b) = .eq := by simp
    rw [ha] at this
    simp at this
    exact this
  -- ugly proof. should be rewritten later.
  by_cases h : l x = 0
  · simp [h, mapDomain]
    rw [DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys] at *
    -- rw [DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys] at h
    simp [Function.Injective.ne_iff this] at *
    intro a b h' h''
    subst h''
    exact h b h'
  · simp [mapDomain]
    rw [eq_comm, DSortedFinsupp.apply_eq_iff_of_apply_ne_zero h,
      DSortedListMap.get?_eq_some_iff_mem_val', DSortedFinsupp.apply_def, DSortedListMap.get?,
      List.findSome?_map]
    simp [Function.comp_def]
    have h₁ := h
    rw [← ne_eq, DSortedFinsupp.apply_ne_zero_iff_get?_val_eq_some_apply,
      DSortedListMap.get?_eq_some_iff_mem_val', DSortedFinsupp.apply_def, DSortedListMap.get?] at h
    convert h
    aesop

@[simp]
lemma mapDomain_apply_eq_zero_of_notin_range [DecidableEq σ] [DecidableEq σ']
    (x' : σ') (hf' : ¬ x' ∈ Set.range f) (l : SortedFinsupp σ R cmp) :
    l.mapDomain f hf x' = 0 := by
  simp at hf'
  rw [DSortedFinsupp.apply_eq_zero_iff_not_mem_val_keys, DSortedListMap.keys, mapDomain]
  simp [hf']

lemma equivFinsupp_mapDomain [DecidableEq σ] [DecidableEq σ']
    {R} [AddCommMonoid R]
    (l : SortedFinsupp σ R cmp) :
    equivFinsupp (l.mapDomain f hf) = (equivFinsupp l).mapDomain f := by
  have : Function.Injective f := by
    intro a b h
    have := hf a b
    rw [h] at this
    have ha : cmp' (f b) (f b) = .eq := by simp
    rw [ha] at this
    simp at this
    exact this
  ext x'
  classical
  by_cases h : x' ∈ Set.range f
  · simp at h
    obtain ⟨x, h⟩ := h
    simp [← h, Finsupp.mapDomain_apply this]
  · simp [mapDomain_apply_eq_zero_of_notin_range (hf' := h), Finsupp.mapDomain_notin_range (h := h)]

lemma mapDomain_eq [DecidableEq σ] [DecidableEq σ'] {R} [AddCommMonoid R]
    (l : SortedFinsupp σ R cmp) :
    l.mapDomain f hf = equivFinsupp.symm ((equivFinsupp l).mapDomain f) := by
  rw [← equivFinsupp_mapDomain (cmp' := cmp') (σ := σ) (σ' := σ')]
  simp
  exact hf

end mapDomain

section embDomain

variable {R' : Type*} [Zero R']
variable {σ' R} [Zero R] {cmp' : σ' → σ' → Ordering} [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
variable (f₁ : σ → σ') (hf₁ : ∀ i j, cmp i j = cmp' (f₁ i) (f₁ j))
variable (f₂ : σ → R → R') (hf₂ : ∀ i, f₂ i 0 = 0) [∀ i : σ, ∀ x : R, Decidable (f₂ i x = 0)]

#check Function.comp

-- do the same work as the composition of `mapDomain` and `mapRange`, but should be faster.
-- low priority.
def embDomain (l : SortedFinsupp σ R cmp) :
    SortedFinsupp σ' R' cmp' :=
  ⟨
    ⟨l.val.val.filterMap
      (fun (a : (_ : σ) × R) ↦ let r := f₂ a.1 a.2; if r = 0 then none else some ⟨f₁ a.1, r⟩),
      by
        have := hf₁ -- write it here so that mapDomainRange will have arguments `hf₂` and `hf₂`
        have := hf₂
        rw [List.chain'_iff_pairwise, List.pairwise_filterMap]
        have orig_sorted : List.Pairwise (λ a b => cmp a.1 b.1 = .lt) l.val.val := by
          rw [← List.chain'_iff_pairwise]
          exact l.val.2
        apply List.Pairwise.imp
        · intro x y h z hz z1 hz2
          simp at hz hz2
          cases' hz with h1 h2
          cases' hz2 with h3 h4
          aesop
        · aesop
    ⟩,
    by
      have := l.2
      simp at this
      simp
      intro a x x1 hx ha
      aesop
  ⟩

-- low priority
lemma embDomain_apply [DecidableEq σ] [DecidableEq σ'] (x : σ) (l : SortedFinsupp σ R cmp) :
    (l.embDomain f₁ hf₁ f₂ hf₂) (f₁ x) = f₂ x (l x) := by sorry


end embDomain

-- section SMul

-- variable {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
-- variable [∀ x : M, ∀ s : R, Decidable (s • x = 0)]


-- def chain'_mulMon' (k : R) (l : List (σ × R)) (h : l.Chain' (cmp ·.1 ·.1 = .lt)) : (mulMon' k l).Chain' (cmp ·.1 ·.1 = .lt) := by
--   induction l with
--   | nil => simp [mulMon']
--   | cons head tail h' =>
--     simp [mulMon', List.chain'_cons'] at *
--     sorry

-- def mulMon (k : R) (l : SortedFinsupp σ R cmp) : SortedFinsupp σ R cmp := ⟨mulMon' k l.val, by
--   exact chain'_mulMon' k l.val l.property
--   sorry
-- ⟩

-- def mul' (p₁ : List (σ × R)) (p₂ : List (σ × R)) [∀ k : R, Decidable (k = 1)] : List (σ × R) :=
--   let p₁l := p₁.lengthTR
--   let p₂l := p₂.lengthTR
--   let fuel := p₁l * p₂l + 1
--   if p₁l < p₂l then
--     go p₁ p₂ fuel []
--   else
--     go p₂ p₁ fuel []
-- where
--   go (p₁ : List (σ × R)) (p₂ : List (σ × R)) (fuel : Nat) (acc : List (σ × R)) : List (σ × R) :=
--     match p₁ with
--     | .nil => acc
--     | .cons (k, m) p₁ => go p₁ p₂ fuel (add' (p₂.mulMon k m cmp) cmp (fuel := fuel))


-- instance : Mul (SortedFinsupp σ R cmp) where
--   mul := sorry

-- end SMul
-- #check Finsupp
