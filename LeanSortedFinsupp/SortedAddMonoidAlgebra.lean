import LeanSortedFinsupp.SortedFinsupp


variable {G : Type*}

variable (G) in
def SortedAddMonoidAlgebra (R : Type*) [Semiring R] (cmp : G → G → Ordering) [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] :=
  SortedFinsupp G R cmp

namespace SortedAddMonoidAlgebra

variable {cmp : G → G → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Basic

variable {R : Type*} [Semiring R]

instance [DecidableEq G] [DecidableEq R] : DecidableEq (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstanceAs <| DecidableEq (SortedFinsupp G R cmp)

instance : Zero (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstanceAs <| Zero (SortedFinsupp G R cmp)

instance instFunLike [DecidableEq G] : FunLike (SortedAddMonoidAlgebra G R cmp) G R :=
  fast_instance% inferInstanceAs <| FunLike (SortedFinsupp G R cmp) G R

lemma ext_iff [DecidableEq G] {l1 l2 : SortedAddMonoidAlgebra G R cmp} :
    l1 = l2 ↔ ∀ s : G, l1 s = l2 s := SortedFinsupp.ext_iff

variable (cmp) in
def single (x : G) (y : R) [Decidable (y = 0)] : SortedAddMonoidAlgebra G R cmp :=
  SortedFinsupp.single cmp x y

@[simp]
lemma single_apply [DecidableEq G] (a : G) (b : R) [Decidable (b = 0)] (c : G) :
    (single cmp a b) c = if a = c then b else 0 := SortedFinsupp.single_apply ..

@[simp]
lemma zero_apply [DecidableEq G] (x : G) : (0 : SortedAddMonoidAlgebra G R cmp) x = 0 := rfl

@[simp]
lemma coe_zero  [DecidableEq G] : ⇑(0 : SortedAddMonoidAlgebra G R cmp) = 0 := rfl

@[simp]
lemma zero_sum [DecidableEq G] [DecidableEq R]
    {R' : Type*} [AddCommMonoid R'] (g : G → R → R') :
    (0 : SortedAddMonoidAlgebra G R cmp).sum g = 0 := rfl

@[simp]
lemma sum_zero {R' : Type*} [AddCommMonoid R'] [DecidableEq G] [DecidableEq R]
    (l : SortedAddMonoidAlgebra G R cmp) :
    l.sum (fun _ _ ↦ 0) = (0 : R') := SortedFinsupp.sum_zero ..

@[ext]
lemma ext [DecidableEq G] {l1 l2 : SortedAddMonoidAlgebra G R cmp}
    (h : ∀ s : G, l1 s = l2 s) :
  l1 = l2 := SortedFinsupp.ext h

instance instAdd [(a : R) → Decidable (a = 0)] :
    Add (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% SortedFinsupp.instAdd

@[simp]
lemma add_apply [DecidableEq G] [(a : R) → Decidable (a = 0)]
    (l₁ l₂ : SortedAddMonoidAlgebra G R cmp) (x : G) :
    (l₁ + l₂) x = l₁ x + l₂ x := SortedFinsupp.add_apply ..

instance instAddMonoid [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    AddMonoid (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstanceAs <| AddMonoid (SortedFinsupp G R cmp)

instance instAddCommMonoid [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    AddCommMonoid (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstanceAs <| AddCommMonoid (SortedFinsupp G R cmp)

instance instSMulWithZero {M} [Zero M] [SMulWithZero M R]
    [∀ y : R, Decidable (y = 0)] :
    SMulWithZero M (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstanceAs <| SMulWithZero M (SortedFinsupp G R cmp)

instance instSMul {M} [Zero M] [SMulWithZero M R] [∀ y : R, Decidable (y = 0)] :
    SMul M (SortedAddMonoidAlgebra G R cmp) :=
  fast_instance% inferInstance

lemma smul_def {M} [Zero M] [SMulWithZero M R] [∀ y : R, Decidable (y = 0)]
    (s : M) (l : SortedAddMonoidAlgebra G R cmp) :
    s • l = l.mapRange (fun _ ↦ (s • ·)) (by simp) := rfl

@[simp]
lemma smul_apply [DecidableEq G] {M} [Zero M] [SMulWithZero M R] [∀ y : R, Decidable (y = 0)]
    (s : M) (l : SortedAddMonoidAlgebra G R cmp) (x : G) :
    (s • l) x = s • (l x) := SortedFinsupp.smul_apply ..

def addEquivAddMonoidAlgebra [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    AddEquiv (SortedAddMonoidAlgebra G R cmp) (AddMonoidAlgebra R G) :=
  SortedFinsupp.addEquivFinsupp

@[simp]
lemma addEquivAddMonoidAlgebra_apply [(a : R) → Decidable (a = 0)] [DecidableEq G]
    (l : SortedAddMonoidAlgebra G R cmp) (x : G) :
    addEquivAddMonoidAlgebra l x = l x := SortedFinsupp.equivFinsupp_apply ..

lemma addEquivAddMonoidAlgebra_zero [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    addEquivAddMonoidAlgebra (0 : SortedAddMonoidAlgebra G R cmp) = 0 := rfl

def singleAddHom [DecidableEq G] [∀ i : R, Decidable (i = 0)] (x : G) :
    R →+ SortedAddMonoidAlgebra G R cmp := {
  SortedFinsupp.singleAddHom x with
  toFun y := single cmp x y
}

end Basic
section Mul

variable {R} [Semiring R] [AddCommMonoid G] [DecidableEq G] [DecidableEq R]
variable [fact : Fact <| ∀ (a i j : G), cmp i j = cmp (a + i) (a + j)]
variable (l₁ l₂ : SortedAddMonoidAlgebra G R cmp)

instance instMul : Mul (SortedAddMonoidAlgebra G R cmp) where
  mul l₁ l₂ := l₁.sum fun a b ↦ (b • l₂).mapDomain (a + ·) (by simp [← fact.elim])

lemma mul_def : l₁ * l₂ =
    l₁.sum fun a b ↦ (b • l₂).mapDomain (a + ·) (by simp [← fact.elim]) := rfl

lemma mul_apply (l₁ l₂ : SortedAddMonoidAlgebra G R cmp) (x : G) :
    (l₁ * l₂) x = l₁.sum fun a₁ b₁ => l₂.sum fun a₂ b₂ => if a₁ + a₂ = x then b₁ * b₂ else 0 := by
  simp [mul_def, l₁.sum_apply', smul_def, SortedFinsupp.mapDomain_eq]
  congr
  ext x' y'
  have (f : G →₀ R) : f = (SkewMonoidAlgebra.ofFinsupp f).toFinsupp := rfl
  rw [this (SortedFinsupp.equivFinsupp _), ← SkewMonoidAlgebra.toFinsupp_mapDomain,
    SkewMonoidAlgebra.mapDomain_apply, SkewMonoidAlgebra.toFinsupp_sum',
    SortedFinsupp.equivFinsupp_symm_apply,
    ← SortedFinsupp.sum_eq_equivFinsupp_sum]
  have :=
    SortedFinsupp.sum_apply (cmp := cmp) (σ := G) (R := R) (f := Finsupp.applyAddHom (M := R) x)
  simp only [Finsupp.applyAddHom_apply] at this
  simp [this]
  congr
  ext
  split_ifs with h
  · simp [h]
  · simp [h]

lemma addEquivAddMonoidAlgebra_mul
    (l₁ l₂ : SortedAddMonoidAlgebra G R cmp) :
    addEquivAddMonoidAlgebra (l₁ * l₂) =
      addEquivAddMonoidAlgebra l₁ * addEquivAddMonoidAlgebra l₂ := by
  ext
  simp [mul_apply, AddMonoidAlgebra.mul_apply, Finsupp.sum.eq_def,
    SortedFinsupp.sum_eq_sum_support]
  rfl

def ringEquivAddMonoidAlgebra :
    RingEquiv (SortedAddMonoidAlgebra G R cmp) (AddMonoidAlgebra R G) := {
    addEquivAddMonoidAlgebra with
    map_mul' := addEquivAddMonoidAlgebra_mul
  }

lemma mul_eq (l₁ l₂ : SortedAddMonoidAlgebra G R cmp) : l₁ * l₂ =
    addEquivAddMonoidAlgebra.symm (addEquivAddMonoidAlgebra l₁ * addEquivAddMonoidAlgebra l₂) := by
  simp [← addEquivAddMonoidAlgebra_mul]

instance instSemiring : Semiring (SortedAddMonoidAlgebra G R cmp) where
  left_distrib a b c := by simp [mul_eq, mul_add]
  right_distrib a b c := by simp [mul_eq, add_mul]
  zero_mul := by simp [ext_iff, mul_apply]
  mul_zero := by simp [ext_iff, mul_apply]
  mul_assoc := by simp [mul_eq, mul_assoc]
  one := single cmp 0 1
  one_mul := by
    convert_to ∀ (a : SortedAddMonoidAlgebra G R cmp), single cmp 0 (1 : R) * a = a
    simp [ext_iff, mul_apply, single]
    simp [SortedFinsupp.sum_eq_sum_support, SortedFinsupp.mem_support_iff]
    simp_intro ..
  mul_one := by
    convert_to ∀ (a : SortedAddMonoidAlgebra G R cmp), a * single cmp 0 (1 : R) = a
    simp [ext_iff, mul_apply, single]
    simp [SortedFinsupp.sum_eq_sum_support, SortedFinsupp.mem_support_iff]
    simp_intro ..

instance instCommSemiring {R} [CommSemiring R] [DecidableEq R] :
    CommSemiring (SortedAddMonoidAlgebra G R cmp) where
  mul_comm := by simp [mul_eq, mul_comm]

#check AddMonoidAlgebra.singleZeroAlgHom
def singleZeroRingHom {R} [DecidableEq R] [Semiring R] :
    R →+* SortedAddMonoidAlgebra G R cmp :=
  { singleAddHom 0 with
    map_one' := rfl
    map_mul' _ _ := by
      ext
      simp [singleAddHom, mul_apply, single]
      -- why `simp` and `simp_rw` doesn't work here?
      rw [SortedFinsupp.single_apply]
    }

end Mul

section Algebra

variable [AddCommMonoid G]
variable {R : Type*} {M} [CommSemiring R] [CommSemiring M] [Algebra M R]
variable [fact : Fact <| ∀ (a i j : G), cmp i j = cmp (a + i) (a + j)]
variable [DecidableEq G] [DecidableEq R]

-- def
#check AddMonoidAlgebra.singleZeroAlgHom
instance : Algebra M (SortedAddMonoidAlgebra G R cmp) where
  algebraMap := singleZeroRingHom.comp (algebraMap M R)
  commutes' _ _ := mul_comm ..
  smul_def' r x := by
    ext
    simp [singleZeroRingHom, singleAddHom, mul_apply, single,
      SortedFinsupp.sum_eq_sum_support, Algebra.smul_def]
    split_ifs with h
    · simp [h]
    · simp [SortedFinsupp.mem_support_iff]
      simp_intro _

def algEquivAddMonoidAlgebra [DecidableEq G] :
    (SortedAddMonoidAlgebra G R cmp) ≃ₐ[M] (AddMonoidAlgebra R G) := {
    ringEquivAddMonoidAlgebra with
    commutes' r := by
      simp [ringEquivAddMonoidAlgebra]
      ext x
      simp [AddMonoidAlgebra.single_apply]
      convert_to (single cmp 0 (algebraMap M R r) : SortedAddMonoidAlgebra G R cmp) x = _
      simp
  }

#check AddMonoidAlgebra.mul_apply

#check AddMonoidAlgebra.toMultiplicative

#check AddMonoidAlgebra.algebra
#check AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
#check AddMonoidAlgebra.domCongr
#check AddMonoidAlgebra.algebra
#check AddMonoidAlgebra.commSemiring
#check AddMonoidAlgebra.semiring
#check Finsupp.instAddCommMonoid
#check Submodule
#check AddMonoidAlgebra.mul_def

end Algebra

section Semiring

variable {R} [Semiring R] [AddCommMonoid G] [DecidableEq G] [DecidableEq R]
variable [fact : Fact <| ∀ (a i j : G), cmp i j = cmp (a + i) (a + j)]
variable (l₁ l₂ : SortedAddMonoidAlgebra G R cmp)

#synth Mul (SortedAddMonoidAlgebra G R cmp)

end Semiring

-- variable {M} [Zero M] [SMulWithZero R M]
-- instance algebra {R k G} [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
--     Algebra R (SortedAddMonoidAlgebra G k cmp) where

-- instance instSMulWithZero : SMulWithZero R (SortedFinsupp G M cmp)
#check List.mergeWith

end SortedAddMonoidAlgebra
