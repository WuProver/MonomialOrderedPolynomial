import LeanExperiments.SortedFinsupp


variable {G : Type*}

variable (G) in
def SortedAddMonoidAlgebra (R : Type*) [Semiring R] (cmp : G → G → Ordering) [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] :=
  SortedFinsupp G R cmp

variable (cmp : G → G → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Basic

variable {R : Type*} [Semiring R]

instance [DecidableEq G] [DecidableEq R] : DecidableEq (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| DecidableEq (SortedFinsupp G R cmp)

instance : Zero (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| Zero (SortedFinsupp G R cmp)

instance instFunLike [DecidableEq G] : FunLike (SortedAddMonoidAlgebra G R cmp) G R :=
  inferInstanceAs <| FunLike (SortedFinsupp G R cmp) G R

instance instAdd [(a : R) → Decidable (a = 0)] :
    Add (SortedAddMonoidAlgebra G R cmp) := SortedFinsupp.instAdd

instance instAddMonoid [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    AddMonoid (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| AddMonoid (SortedFinsupp G R cmp)

instance instAddCommMonoid [(a : R) → Decidable (a = 0)] [DecidableEq G] :
    AddCommMonoid (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| AddCommMonoid (SortedFinsupp G R cmp)

instance instSMulWithZero {M} [Zero M] [SMulWithZero M R] [∀ y : R, Decidable (y = 0)] :
    SMulWithZero M (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| SMulWithZero M (SortedFinsupp G R cmp)

lemma smul_def {M} [Zero M] [SMulWithZero M R] [∀ y : R, Decidable (y = 0)]
    (s : M) (l : SortedAddMonoidAlgebra G R cmp) :
    s • l = l.mapRange (fun _ ↦ (s • ·)) (by simp) := rfl

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
  simp at this
  simp [this]
  congr
  ext
  split_ifs with h
  · simp [h]
  · simp [h]

#check SkewMonoidAlgebra.mapDomain

lemma equivFinsupp_mul (l₁ l₂ : SortedAddMonoidAlgebra G R cmp) (x : G) :
    (l₁ * l₂) x = l₁.sum fun a₁ b₁ => l₂.sum fun a₂ b₂ => if a₁ + a₂ = x then b₁ * b₂ else 0 := by
  rw [mul_apply]

#check AddMonoidAlgebra.mul_apply

#check AddMonoidAlgebra.toMultiplicative

#check AddMonoidAlgebra.algebra
#check AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
#check AddMonoidAlgebra.domCongr
#check AddMonoidAlgebra.algebra
#check AddMonoidAlgebra.commSemiring
#check Finsupp.instAddCommMonoid
#check Submodule
#check AddMonoidAlgebra.mul_def

end Mul


-- variable {M} [Zero M] [SMulWithZero R M]
-- instance algebra {R k G} [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
--     Algebra R (SortedAddMonoidAlgebra G k cmp) where

-- instance instSMulWithZero : SMulWithZero R (SortedFinsupp G M cmp)
#check List.mergeWith
