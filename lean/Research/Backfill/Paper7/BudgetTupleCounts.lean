import Mathlib

/-! Stars and bars for exact tuples and tuples with a slack coordinate. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Budget

abbrev ExactTuple (k n : ℕ) := {f : Fin k → ℕ // ∑ i, f i = n}

#print axioms Paper7Budget.ExactTuple

instance exactTupleFintype (k n : ℕ) : Fintype (ExactTuple k n) :=
  Fintype.ofEquiv (Sym (Fin k) n) (Sym.equivNatSumOfFintype (Fin k) n)

#print axioms Paper7Budget.exactTupleFintype

theorem card_exactTuple (k n : ℕ) :
    Fintype.card (ExactTuple (k + 1) n) = (n + k).choose k := by
  calc
    Fintype.card (ExactTuple (k + 1) n) = Fintype.card (Sym (Fin (k + 1)) n) :=
      (Fintype.card_congr (Sym.equivNatSumOfFintype (Fin (k + 1)) n)).symm
    _ = (k + 1 + n - 1).choose n := by
      simpa only [Fintype.card_fin] using
        (Sym.card_sym_eq_choose (α := Fin (k + 1)) n)
    _ = (n + k).choose k := by
      have hs : k + 1 + n - 1 = n + k := by omega
      rw [hs]
      exact Nat.choose_symm_of_eq_add rfl

#print axioms Paper7Budget.card_exactTuple

abbrev BoundedTuple (k B : ℕ) := {f : Fin k → ℕ // ∑ i, f i ≤ B}

#print axioms Paper7Budget.BoundedTuple

def boundedTupleEquivExact (k B : ℕ) : BoundedTuple k B ≃ ExactTuple (k + 1) B where
  toFun p := ⟨Fin.cons (B - ∑ i, p.val i) p.val, by
    simpa only [Fin.sum_cons] using Nat.sub_add_cancel p.property⟩
  invFun f := ⟨Fin.tail f.val, by
    have hf : f.val 0 + (∑ i, Fin.tail f.val i) = B := by
      simpa only [Fin.sum_univ_succ, Fin.tail] using f.property
    omega⟩
  left_inv p := by
    apply Subtype.ext
    change Fin.tail (α := fun _ : Fin (k + 1) => ℕ)
      (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) (B - ∑ i, p.val i) p.val) = p.val
    exact Fin.tail_cons (α := fun _ : Fin (k + 1) => ℕ) _ _
  right_inv f := by
    apply Subtype.ext
    change Fin.cons (B - ∑ i, Fin.tail f.val i) (Fin.tail f.val) = f.val
    have hf : f.val 0 + (∑ i, Fin.tail f.val i) = B := by
      simpa only [Fin.sum_univ_succ, Fin.tail] using f.property
    have hfirst : B - (∑ i, Fin.tail f.val i) = f.val 0 := by omega
    rw [hfirst, Fin.cons_self_tail]

#print axioms Paper7Budget.boundedTupleEquivExact

instance boundedTupleFintype (k B : ℕ) : Fintype (BoundedTuple k B) :=
  Fintype.ofEquiv (ExactTuple (k + 1) B) (boundedTupleEquivExact k B).symm

#print axioms Paper7Budget.boundedTupleFintype

theorem card_boundedTuple (k B : ℕ) :
    Fintype.card (BoundedTuple k B) = (B + k).choose k :=
  (Fintype.card_congr (boundedTupleEquivExact k B)).trans (card_exactTuple k B)

#print axioms Paper7Budget.card_boundedTuple

end Paper7Budget
