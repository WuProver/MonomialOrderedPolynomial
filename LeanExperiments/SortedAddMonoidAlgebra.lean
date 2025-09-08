import LeanExperiments.SortedFinsupp

variable {G : Type*} {R : Type*} [Semiring R] (cmp : G → G → Ordering)
variable [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

variable (G R) in
def SortedAddMonoidAlgebra :=
  SortedFinsupp G R cmp

instance [DecidableEq G] [DecidableEq R] : DecidableEq (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| DecidableEq (SortedFinsupp G R cmp)

instance : Zero (SortedAddMonoidAlgebra G R cmp) :=
  inferInstanceAs <| Zero (SortedFinsupp G R cmp)

instance instFunLike [DecidableEq G] : FunLike (SortedAddMonoidAlgebra G R cmp) G R :=
  inferInstanceAs <| FunLike (SortedFinsupp G R cmp) G R

instance instAdd [(a : R) → Decidable (a = 0)] :
    Add (SortedAddMonoidAlgebra G R cmp) := SortedFinsupp.instAdd

section Mul

variable [Add G]

-- instance instMul [(a : R) → Decidable (a = 0)] : Mul (SortedAddMonoidAlgebra G R cmp) :=
--   ⟨fun f g => f.sum <| fun ⟩

#check AddMonoidAlgebra.semiring
#check AddMonoidAlgebra.algebra
#check AddMonoidAlgebra.domCongr
#check AddMonoidAlgebra.algebra
#check Finsupp.instAddCommMonoid
#check Submodule
#check AddMonoidAlgebra.mul_def

end Mul


-- variable {M} [Zero M] [SMulWithZero R M]
-- instance algebra {R k G} [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
--     Algebra R (SortedAddMonoidAlgebra G k cmp) where

-- instance instSMulWithZero : SMulWithZero R (SortedFinsupp G M cmp)
#check List.mergeWith
