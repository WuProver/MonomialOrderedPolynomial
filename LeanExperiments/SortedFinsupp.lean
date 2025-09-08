import LeanExperiments.DSortedFinsupp

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

lemma support_finite [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    (Function.support l).Finite := by simp [← toFinset_support]

instance : IsAntisymm (α := σ) (cmp · · |>.isLE) where
  antisymm _ _ h h' := Std.LawfulEqCmp.eq_of_compare (Std.OrientedCmp.isLE_antisymm h h')

instance : IsAntisymm (α := σ) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

instance : IsTrans (α := σ) (cmp · · |>.isLE) where
  trans _ _ _ := Std.TransCmp.isLE_trans

instance : IsTrans (α := σ) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

instance : IsTotal (α := σ) (cmp · · |>.isLE) where
  total a b := by
    rw [or_iff_not_imp_left]
    intro h
    simp [Std.OrientedCmp.lt_of_not_isLE h]

instance : IsTotal (α := σ) (cmp · · ≠ .gt) := by
  simp [Ordering.ne_gt_iff_isLE]
  exact inferInstance

variable (cmp) in
def onSupport (f : σ → R) (s : Finset σ)
    (h : ∀ x, x ∈ s ↔ f x ≠ 0) :
    SortedFinsupp σ R cmp := DSortedFinsupp.onSupport cmp f s h

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

lemma support_eq_equivFinsupp_support [DecidableEq σ] (l : SortedFinsupp σ R cmp) :
    l.support.toFinset = (equivFinsupp l).support := by
  ext x
  simp [mem_support_iff]

end Finsupp

section mergeWith

variable {R : Type*} [Zero R] [∀ a : R, Decidable (a = 0)]
variable (mergeFn : (k : σ) → R → R → R)
variable (l₁ l₂ : SortedFinsupp σ R cmp)

def mergeWith : SortedFinsupp σ R cmp := DSortedFinsupp.mergeWith mergeFn l₁ l₂

@[simp]
lemma mergeWith_apply [DecidableEq σ] (a : σ)
    (hzero : ∀ b : R, mergeFn a b 0 = b)
    (hzero' : ∀ b : R, mergeFn a 0 b = b) :
    (l₁.mergeWith mergeFn l₂ a) = mergeFn a (l₁ a) (l₂ a) :=
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

private def example2 : SortedFinsupp Int Int compare := ⟨⟨[⟨1, 5⟩, ⟨3, 4⟩], by decide⟩, by decide⟩

#reduce example1 + example2

end Add

section mapRange

variable {β₁ β₂ : Type*} [Zero β₁] [Zero β₂]

#check Finsupp.mapRange_apply

def mapRange (f : (k : σ) → β₁ → β₂) (hf : ∀ i, f i 0 = 0)
    [∀ i : σ, ∀ x : β₁, Decidable (f i x = 0)] (l : SortedFinsupp σ β₁ cmp) :
    SortedFinsupp σ β₂ cmp := DSortedFinsupp.mapRange f hf l

@[simp]
def mapRange_apply [DecidableEq σ] {f : (k : σ) → β₁ → β₂} (hf : ∀ i, f i 0 = 0)
    [∀ i : σ, ∀ x : β₁, Decidable (f i x = 0)] (l : SortedFinsupp σ β₁ cmp) (x : σ) :
    l.mapRange f hf x = f x (l x) := DSortedFinsupp.mapRange_apply ..

end mapRange

section mapDomain

#check Finsupp.mapDomain

end mapDomain

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

end SumProd

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

section mapDomain

variable {σ' R} [Zero R] {cmp' : σ' → σ' → Ordering} [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']

def mapDomain (f : σ → σ') (hf : ∀ i j, cmp i j = cmp' (f i) (f j)) (l : SortedFinsupp σ R cmp) :
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
lemma mapDomain_apply [DecidableEq σ] (f : σ → σ') (hf : ∀ i j, cmp i j = cmp' (f i) (f j))
    (x : σ) (l : SortedFinsupp σ R cmp) :
  l.mapDomain f hf (f x) = l x := sorry


end mapDomain

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
