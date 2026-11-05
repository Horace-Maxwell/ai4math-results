import Research.Backfill.Paper7.MomentB6TenRoute
import Research.Backfill.Paper7.MomentB6DominantWeights

/-! Source-only exact truncated-tail fibre for every dimension and every Q.
This bridge imposes no dominant-coordinate hypothesis. Both endpoints of the
recovered pivot coordinate are kept, including the original Q=0/1 cases. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def BoundedTailSlice (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) : Prop :=
  (∑ k, boundedTailValue n z i a k) ≤ Q ∧
    Q ≤ z i + (∑ k, boundedTailValue n z i a k)
#print axioms Paper7MomentCounts.BoundedTailSlice

theorem boundedTailValue_restriction_add_at (n : ℕ) (z : Fin n → ℕ) (i : Fin n)
    (q : (k : Fin n) → Fin (z k + 1)) :
    (∑ k, boundedTailValue n z i (fun j => q j.val) k) + (q i).val =
      ∑ k, (q k).val := by
  have ht := Finset.sum_erase_add Finset.univ
    (boundedTailValue n z i (fun j => q j.val)) (Finset.mem_univ i)
  have hz : boundedTailValue n z i (fun j => q j.val) i = 0 := by simp [boundedTailValue]
  have hs : (∑ k ∈ Finset.univ.erase i, boundedTailValue n z i (fun j => q j.val) k) =
      ∑ k ∈ Finset.univ.erase i, (q k).val := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [boundedTailValue,dite_eq_right (Finset.mem_erase.mp hk).1]
  rw [hz,add_zero,hs] at ht
  rw [← ht]
  exact Finset.sum_erase_add Finset.univ (fun k => (q k).val) (Finset.mem_univ i)
#print axioms Paper7MomentCounts.boundedTailValue_restriction_add_at

def boundedSlicedAssignment (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1))
    (ha : BoundedTailSlice n z i Q a) : (k : Fin n) → Fin (z k + 1) := fun k =>
  if hk : k = i then ⟨Q - ∑ j, boundedTailValue n z i a j,by
    subst k
    have h := ha.2
    omega⟩ else a ⟨k,hk⟩
#print axioms Paper7MomentCounts.boundedSlicedAssignment

theorem boundedSlicedAssignment_sum (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1))
    (ha : BoundedTailSlice n z i Q a) :
    (∑ k, (boundedSlicedAssignment n z i Q a ha k).val) = Q := by
  have hb := ha.1
  have he := Finset.sum_erase_add Finset.univ
    (fun k => (boundedSlicedAssignment n z i Q a ha k).val) (Finset.mem_univ i)
  have ht := Finset.sum_erase_add Finset.univ (boundedTailValue n z i a) (Finset.mem_univ i)
  have hz : boundedTailValue n z i a i = 0 := by simp [boundedTailValue]
  have hi : (boundedSlicedAssignment n z i Q a ha i).val =
      Q - ∑ k, boundedTailValue n z i a k := by simp [boundedSlicedAssignment]
  have hs : (∑ k ∈ Finset.univ.erase i, (boundedSlicedAssignment n z i Q a ha k).val) =
      ∑ k ∈ Finset.univ.erase i, boundedTailValue n z i a k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp hk).1
    simp only [boundedSlicedAssignment,boundedTailValue,dite_eq_right hki]
  rw [hi,hs] at he
  rw [hz,add_zero] at ht
  omega
#print axioms Paper7MomentCounts.boundedSlicedAssignment_sum

def boundedSlicedFibreEquiv (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ) :
    {a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1) // BoundedTailSlice n z i Q a} ≃
      {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = Q} where
  toFun a := ⟨boundedSlicedAssignment n z i Q a.val a.property,
    boundedSlicedAssignment_sum n z i Q a.val a.property⟩
  invFun q := ⟨fun k => q.val k.val,by
    have he := boundedTailValue_restriction_add_at n z i q.val
    rw [q.property] at he
    have hb := (q.val i).isLt
    exact ⟨by omega,by omega⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext k
    simp only [boundedSlicedAssignment,dite_eq_right k.property]
  right_inv q := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    by_cases hki : k = i
    · subst k
      have he := boundedTailValue_restriction_add_at n z i q.val
      rw [q.property] at he
      simp only [boundedSlicedAssignment,↓reduceDIte]
      omega
    · simp only [boundedSlicedAssignment,dite_eq_right hki]
#print axioms Paper7MomentCounts.boundedSlicedFibreEquiv

theorem boundedQDP_sliced_fibre_card (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ) :
    Paper7MomentDP.boundedQDP n z Q =
      Nat.card {a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1) // BoundedTailSlice n z i Q a} := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  exact Nat.card_congr (boundedSlicedFibreEquiv n z i Q).symm
#print axioms Paper7MomentCounts.boundedQDP_sliced_fibre_card

theorem boundedQDP_sliced_sum (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ) :
    Paper7MomentDP.boundedQDP n z Q =
      ∑ a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1),
        if BoundedTailSlice n z i Q a then 1 else 0 := by
  classical
  rw [boundedQDP_sliced_fibre_card n z i Q,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp
#print axioms Paper7MomentCounts.boundedQDP_sliced_sum

theorem b6_total_ten_half_Q_weight (z : Fin 6 → ℕ) (hZ : (∑ k, z k) = 10)
    (Q : ℕ) (hQ : Q ≤ 10) :
    Paper7MomentDP.boundedQDP 6 z Q = Paper7MomentDP.boundedQDP 6 z (min Q (10-Q)) ∧
      min Q (10-Q) ≤ 5 := by
  by_cases hle : Q ≤ 5
  · have hm : min Q (10-Q) = Q := min_eq_left (by omega)
    exact ⟨by rw [hm],by omega⟩
  · have hm : min Q (10-Q) = 10-Q := min_eq_right (by omega)
    have hc := boundedQDP_complement 6 z Q (by omega)
    rw [hZ] at hc
    exact ⟨by rw [hm]; exact hc,by omega⟩
#print axioms Paper7MomentCounts.b6_total_ten_half_Q_weight

end Paper7MomentCounts
