import Mathlib

variable {σ R : Type*} [Semiring R]

inductive TreeRepr (σ : Type*) (R : Type*) where
  | const : R → TreeRepr σ R
  | var : σ → TreeRepr σ R
  | add : TreeRepr σ R → TreeRepr σ R → TreeRepr σ R
  | mul : TreeRepr σ R → TreeRepr σ R → TreeRepr σ R
  | pow : TreeRepr σ R → ℕ → TreeRepr σ R
  | ref : TreeRepr σ R → TreeRepr σ R
with
  @[computed_field, semireducible]
  totalDegreeBound : ∀ (σ) (R), TreeRepr σ R → ℕ
    | _, _, .const _ => 0
    | _, _, .var _ => 1
    | _, _, .add p q => max p.totalDegreeBound q.totalDegreeBound
    | _, _, .mul p q => max p.totalDegreeBound q.totalDegreeBound
    | _, _, .pow p n => p.totalDegreeBound * n
    | _, _, .ref p => p.totalDegreeBound

  -- @[computed_field]
  -- powDepth_ : ∀ (σ) (R), TreeRepr σ R → ℕ
  -- | _, _, .const _ => 0
  -- | _, _, .var _ => 0
  -- | _, _, .add p q => 0 --max p.powDepth_ q.powDepth_
  -- | _, _, .mul p q => 0 --max p.powDepth_ q.powDepth_
  -- | _, _, .pow p n => 0 --n + p.powDepth_
  -- | _, _, .ref p => 0 --p.powDepth_
deriving Repr

def TreeRepr.eval (p : TreeRepr σ R) (f : σ → R) : R :=
  match p with
  | const c => c
  | var v => f v
  | add p q => p.eval f + q.eval f
  | mul p q => p.eval f * q.eval f
  | pow p n => (p.eval f) ^ n
  | ref p => p.eval f

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] [Nontrivial R] (p q : MvPolynomial σ R)

noncomputable def _root_.TreeRepr.toMvPolynomial : TreeRepr σ R → MvPolynomial σ R
  | .const c => .C c
  | .var v => .X v
  | .add p q => p.toMvPolynomial + q.toMvPolynomial
  | .mul p q => p.toMvPolynomial * q.toMvPolynomial
  | .pow p n => p.toMvPolynomial ^ n
  | .ref p => p.toMvPolynomial

class PolyRepr (p : MvPolynomial σ R) where
  tree : TreeRepr σ R
  tree_eq : tree.toMvPolynomial = p

section PolyRepr

def toRepr [p_repr : p.PolyRepr] := p_repr

instance {c} : (C c : MvPolynomial σ R).PolyRepr where
  tree := .const c
  tree_eq := rfl

instance {v} : (X v : MvPolynomial σ R).PolyRepr where
  tree := .var v
  tree_eq := rfl

instance [p.PolyRepr] [q.PolyRepr] : (p * q).PolyRepr where
  tree := .mul p.toRepr.tree q.toRepr.tree
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rfl

instance [p.PolyRepr] [q.PolyRepr] : (p + q).PolyRepr where
  tree := .add p.toRepr.tree q.toRepr.tree
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rfl

instance [p.PolyRepr] {n : ℕ} : (p ^ n).PolyRepr where
  tree := .pow p.toRepr.tree n
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq]
    rfl

instance {R} [CommRing R] {p q : MvPolynomial σ R} [p.PolyRepr] [q.PolyRepr] :
    (p - q).PolyRepr where
  tree := .add p.toRepr.tree (.mul (.const (-1)) q.toRepr.tree)
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rw [sub_eq_add_neg]
    nth_rw 2 [neg_eq_neg_one_mul]
    nth_rw 1 [TreeRepr.toMvPolynomial]
    congr
    rw [TreeRepr.toMvPolynomial, TreeRepr.toMvPolynomial]
    simp

instance {R} [CommRing R] {p : MvPolynomial σ R} [p.PolyRepr] :
    (- p).PolyRepr where
  tree := .mul (.const (-1)) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toMvPolynomial]
    rw [TreeRepr.toMvPolynomial]
    rw [p.toRepr.tree_eq]
    simp

instance {R} [CommRing R] {p : MvPolynomial σ R} {s : R} [p.PolyRepr] :
    (s • p).PolyRepr where
  tree := .mul (.const s) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toMvPolynomial]
    rw [TreeRepr.toMvPolynomial]
    rw [p.toRepr.tree_eq]
    rw [MvPolynomial.smul_eq_C_mul]

instance {R} [CommRing R] {p : MvPolynomial σ R} {n : Nat} [p.PolyRepr] :
    (n • p).PolyRepr where
  tree := .mul (.const n) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toMvPolynomial]
    rw [TreeRepr.toMvPolynomial]
    rw [p.toRepr.tree_eq]
    simp

instance {R} [CommRing R] {p : MvPolynomial σ R} {n : Int} [p.PolyRepr] :
    (n • p).PolyRepr where
  tree := .mul (.const n) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toMvPolynomial]
    rw [TreeRepr.toMvPolynomial]
    rw [p.toRepr.tree_eq]
    simp

instance : (0 : MvPolynomial σ R).PolyRepr where
  tree := .const 0
  tree_eq := by
    rw [← MvPolynomial.C_0]
    rfl

instance : (1 : MvPolynomial σ R).PolyRepr where
  tree := .const 1
  tree_eq := rfl

instance {n : Nat} [Nat.AtLeastTwo n] : (ofNat(n) : MvPolynomial σ R).PolyRepr where
  tree := .const n
  tree_eq := by
    rw [TreeRepr.toMvPolynomial]
    rfl

#check (X 0 + 4 : MvPolynomial Nat Int).toRepr

end PolyRepr
end MvPolynomial

namespace Polynomial
variable (p q : Polynomial R)

noncomputable def _root_.TreeRepr.toPolynomial (t : TreeRepr σ R) : Polynomial R :=
  match t with
  | .const c => .C c
  | .var _ => .X
  | .add p q => p.toPolynomial + q.toPolynomial
  | .mul p q => p.toPolynomial * q.toPolynomial
  | .pow p n => p.toPolynomial ^ n
  | .ref p => p.toPolynomial

class PolyRepr (p : Polynomial R) where
  tree : TreeRepr Unit R
  tree_eq : tree.toPolynomial = p

def toRepr [p_repr : p.PolyRepr] := p_repr

instance {c} : (C c : Polynomial R).PolyRepr where
  tree := .const c
  tree_eq := rfl

instance : (X : Polynomial R).PolyRepr where
  tree := .var 0
  tree_eq := rfl

instance [p.PolyRepr] [q.PolyRepr] : (p * q).PolyRepr where
  tree := .mul p.toRepr.tree q.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq, q.toRepr.tree_eq]

instance [p.PolyRepr] [q.PolyRepr] : (p + q).PolyRepr where
  tree := .add p.toRepr.tree q.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq, q.toRepr.tree_eq]

instance [p.PolyRepr] {n : ℕ} : (p ^ n).PolyRepr where
  tree := .pow p.toRepr.tree n
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq]

instance {R} [CommRing R] {p q : Polynomial R} [p.PolyRepr] [q.PolyRepr] :
    (p - q).PolyRepr where
  tree := .add p.toRepr.tree (.mul (.const (-1)) q.toRepr.tree)
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rw [sub_eq_add_neg]
    nth_rw 2 [neg_eq_neg_one_mul]
    nth_rw 1 [TreeRepr.toPolynomial]
    congr
    rw [TreeRepr.toPolynomial, TreeRepr.toPolynomial]
    simp

instance {R} [CommRing R] {p : Polynomial R} [p.PolyRepr] :
    (-p).PolyRepr where
  tree := .mul (.const (-1)) p.toRepr.tree
  tree_eq := by
    unfold TreeRepr.toPolynomial
    rw [p.toRepr.tree_eq]
    unfold TreeRepr.toPolynomial
    simp

instance : (0 : Polynomial R).PolyRepr where
  tree := .const 0
  tree_eq := by simp [TreeRepr.toPolynomial]

instance : (1 : Polynomial R).PolyRepr where
  tree := .const 1
  tree_eq := by simp [TreeRepr.toPolynomial]


instance {p : Polynomial R} {s : R} [p.PolyRepr] :
    (s • p).PolyRepr where
  tree := .mul (.const s) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial]
    rw [TreeRepr.toPolynomial]
    rw [p.toRepr.tree_eq]
    rw [Polynomial.smul_eq_C_mul]

instance {p : Polynomial R} {n : Nat} [p.PolyRepr] :
    (n • p).PolyRepr where
  tree := .mul (.const n) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial]
    rw [TreeRepr.toPolynomial]
    rw [p.toRepr.tree_eq]
    simp

instance {R} [Ring R] {p : Polynomial R} {n : Int} [p.PolyRepr] :
    (n • p).PolyRepr where
  tree := .mul (.const n) p.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial]
    rw [TreeRepr.toPolynomial]
    rw [p.toRepr.tree_eq]
    simp

instance {n : Nat} [Nat.AtLeastTwo n] : (ofNat(n) : Polynomial R).PolyRepr where
  tree := .const n
  tree_eq := by
    rw [TreeRepr.toPolynomial]
    rfl

#check (X + 4 : Polynomial Int).toRepr

end Polynomial
