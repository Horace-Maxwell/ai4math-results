import Research.Backfill.Paper7.MomentB6EightSupport

/-! Source-only candidate. A generic genuine bounded-q fibre has exactly two
assignments for capacities(M,1), distinct positions and1<=Q<=M. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6TwoPointUnitAssignment (M : ℕ) (i j : Fin 6) (Q : ℕ) (hQ : Q ≤ M)
    (b : Fin 2) : (k : Fin 6) → Fin (b6TwoPointUnit M i j k + 1) := fun k =>
  ⟨if k = i then Q - b.val else if k = j then b.val else 0,by
    by_cases hki : k = i
    · subst k
      simpa [b6TwoPointUnit] using
        Nat.lt_succ_of_le ((Nat.sub_le Q b.val).trans hQ)
    · by_cases hkj : k = j
      · subst k
        simpa [b6TwoPointUnit,hki] using b.isLt
      · simp [b6TwoPointUnit,hki,hkj]⟩
#print axioms Paper7MomentCounts.b6TwoPointUnitAssignment

theorem b6TwoPointUnitAssignment_sum (M : ℕ) (i j : Fin 6) (hij : i ≠ j)
    (Q : ℕ) (hpos : 1 ≤ Q) (hQ : Q ≤ M) (b : Fin 2) :
    (∑ k, (b6TwoPointUnitAssignment M i j Q hQ b k).val) = Q := by
  have hbQ : b.val ≤ Q := by have hb := b.isLt; omega
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp [b6TwoPointUnitAssignment,hij.symm,Nat.sub_add_cancel hbQ]
  · intro k _hk hne
    simp [b6TwoPointUnitAssignment,hne.1,hne.2]
#print axioms Paper7MomentCounts.b6TwoPointUnitAssignment_sum

def b6TwoPointUnitQFibreEquiv (M : ℕ) (i j : Fin 6) (hij : i ≠ j)
    (Q : ℕ) (hpos : 1 ≤ Q) (hQ : Q ≤ M) :
    Fin 2 ≃ {q : (k : Fin 6) → Fin (b6TwoPointUnit M i j k + 1) //
      ∑ k, (q k).val = Q} where
  toFun b := ⟨b6TwoPointUnitAssignment M i j Q hQ b,
    b6TwoPointUnitAssignment_sum M i j hij Q hpos hQ b⟩
  invFun q := ⟨(q.val j).val,by
    have h := (q.val j).isLt
    simpa [b6TwoPointUnit,hij.symm] using h⟩
  left_inv b := by
    apply Fin.ext
    simp [b6TwoPointUnitAssignment,hij.symm]
  right_inv q := by
    have hout (k : Fin 6) (hki : k ≠ i) (hkj : k ≠ j) : (q.val k).val = 0 := by
      have h := (q.val k).isLt
      simp only [b6TwoPointUnit,ite_eq_right hki,ite_eq_right hkj] at h
      omega
    have hs : (q.val i).val + (q.val j).val = Q := by
      have he : (∑ k, (q.val k).val) = (q.val i).val + (q.val j).val := by
        apply Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
        intro k _hk hne
        exact hout k hne.1 hne.2
      exact he.symm.trans q.property
    apply Subtype.ext
    funext k
    apply Fin.ext
    by_cases hki : k = i
    · subst k
      simp only [b6TwoPointUnitAssignment, ↓reduceIte]
      omega
    · by_cases hkj : k = j
      · subst k
        simp [b6TwoPointUnitAssignment,hij.symm]
      · simp [b6TwoPointUnitAssignment,hki,hkj,hout k hki hkj]
#print axioms Paper7MomentCounts.b6TwoPointUnitQFibreEquiv

theorem boundedQDP_twoPointUnit_eq_two (M : ℕ) (i j : Fin 6) (hij : i ≠ j)
    (Q : ℕ) (hpos : 1 ≤ Q) (hQ : Q ≤ M) :
    Paper7MomentDP.boundedQDP 6 (b6TwoPointUnit M i j) Q = 2 := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  calc
    Nat.card {q : (k : Fin 6) → Fin (b6TwoPointUnit M i j k + 1) //
        ∑ k, (q k).val = Q} = Nat.card (Fin 2) :=
      Nat.card_congr (b6TwoPointUnitQFibreEquiv M i j hij Q hpos hQ).symm
    _ = 2 := by simp
#print axioms Paper7MomentCounts.boundedQDP_twoPointUnit_eq_two

end Paper7MomentCounts
