import MonomialOrderedPolynomial.SortedFinsupp
-- import MonomialOrderedPolynomial.Ordering
import MonomialOrderedPolynomial.MonomialOrder

namespace SortedFinsupp


variable {σ : Type*} [DecidableEq σ] [LinearOrder σ]
  {cmp : σ → σ → Ordering}
  {R : Type*} [Zero R]

class _root_.Finsupp.SortedRepr (f : σ →₀ R) where
  repr : SortedFinsupp σ R compare
  eq : repr.toFinsupp = f

def _root_.Finsupp.toSortedRepr (f : σ →₀ R) [inst : f.SortedRepr] :
    Finsupp.SortedRepr f := inst

instance (f : σ →₀ R) [inst : f.SortedRepr] :
    Finsupp.SortedRepr (toLex f) :=
  inferInstanceAs <| Finsupp.SortedRepr f

instance {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [CanonicallyOrderedAdd R] [Sub R] [OrderedSub R]
    [(a : R) → Decidable (a = 0)]
    (f f' : σ →₀ R) [inst : f.SortedRepr] [inst' : f'.SortedRepr] :
    (f - f').SortedRepr where
  repr := inst.repr - inst'.repr
  eq := by
    simp [inst.eq, inst'.eq]
