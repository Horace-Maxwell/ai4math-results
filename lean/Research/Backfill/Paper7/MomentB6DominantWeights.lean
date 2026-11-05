import Research.Backfill.Paper7.MomentB6NineRoute

/-! Source-only generic exact q-fibre elimination.  The dominant coordinate is
recovered from the original total; every other bounded coordinate is retained.
The hypotheses describe the actual interval in which no other-coordinate
assignment is truncated.  They are not assumptions on any original main check.
The complement equivalence retains Q=0 and full-capacity endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def boundedQComplement (n : ℕ) (z : Fin n → ℕ)
    (q : (k : Fin n) → Fin (z k + 1)) : (k : Fin n) → Fin (z k + 1) :=
  fun k => ⟨z k - (q k).val,by have h := Nat.sub_le (z k) (q k).val; omega⟩
#print axioms Paper7MomentCounts.boundedQComplement

theorem boundedQComplement_sum (n : ℕ) (z : Fin n → ℕ)
    (q : (k : Fin n) → Fin (z k + 1)) :
    (∑ k, (boundedQComplement n z q k).val) = (∑ k, z k) - (∑ k, (q k).val) := by
  apply Finset.sum_tsub_distrib
  intro k _hk
  have h := (q k).isLt
  omega
#print axioms Paper7MomentCounts.boundedQComplement_sum

theorem boundedQComplement_involutive (n : ℕ) (z : Fin n → ℕ) :
    Function.Involutive (boundedQComplement n z) := by
  intro q
  funext k
  apply Fin.ext
  have h := (q k).isLt
  change z k - (z k - (q k).val) = (q k).val
  omega
#print axioms Paper7MomentCounts.boundedQComplement_involutive

def boundedQComplementFibreEquiv (n : ℕ) (z : Fin n → ℕ) (Q : ℕ)
    (hQ : Q ≤ ∑ k, z k) :
    {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = Q} ≃
      {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = (∑ k, z k) - Q} where
  toFun q := ⟨boundedQComplement n z q.val,by rw [boundedQComplement_sum,q.property]⟩
  invFun q := ⟨boundedQComplement n z q.val,by
    rw [boundedQComplement_sum,q.property]
    omega⟩
  left_inv q := Subtype.ext (boundedQComplement_involutive n z q.val)
  right_inv q := Subtype.ext (boundedQComplement_involutive n z q.val)
#print axioms Paper7MomentCounts.boundedQComplementFibreEquiv

theorem boundedQDP_complement (n : ℕ) (z : Fin n → ℕ) (Q : ℕ)
    (hQ : Q ≤ ∑ k, z k) :
    Paper7MomentDP.boundedQDP n z Q = Paper7MomentDP.boundedQDP n z ((∑ k, z k) - Q) := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card,Paper7MomentDP.boundedQDP_eq_fibre_card]
  exact Nat.card_congr (boundedQComplementFibreEquiv n z Q hQ)
#print axioms Paper7MomentCounts.boundedQDP_complement

def boundedTailValue (n : ℕ) (z : Fin n → ℕ) (i : Fin n)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) : Fin n → ℕ :=
  fun k => if hk : k = i then 0 else (a ⟨k,hk⟩).val
#print axioms Paper7MomentCounts.boundedTailValue

theorem boundedTailValue_sum_le (n : ℕ) (z : Fin n → ℕ) (i : Fin n)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) :
    (∑ k, boundedTailValue n z i a k) ≤ ∑ k ∈ Finset.univ.erase i, z k := by
  have he := Finset.sum_erase_add Finset.univ (boundedTailValue n z i a) (Finset.mem_univ i)
  have hz : boundedTailValue n z i a i = 0 := by simp [boundedTailValue]
  rw [hz,add_zero] at he
  rw [← he]
  apply Finset.sum_le_sum
  intro k hk
  have hki := (Finset.mem_erase.mp hk).1
  have hb := (a ⟨k,hki⟩).isLt
  change (a ⟨k,hki⟩).val < z k + 1 at hb
  simp only [boundedTailValue,dite_eq_right hki]
  omega
#print axioms Paper7MomentCounts.boundedTailValue_sum_le

def boundedDominantAssignment (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (hQ : Q ≤ z i) (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) :
    (k : Fin n) → Fin (z k + 1) := fun k =>
  if hk : k = i then ⟨Q - ∑ j, boundedTailValue n z i a j,by
    subst k
    have hb := Nat.sub_le Q (∑ j, boundedTailValue n z i a j)
    omega⟩ else a ⟨k,hk⟩
#print axioms Paper7MomentCounts.boundedDominantAssignment

theorem boundedDominantAssignment_sum (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (hQ : Q ≤ z i) (hrest : (∑ k ∈ Finset.univ.erase i, z k) ≤ Q)
    (a : (k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) :
    (∑ k, (boundedDominantAssignment n z i Q hQ a k).val) = Q := by
  have hb := (boundedTailValue_sum_le n z i a).trans hrest
  have he := Finset.sum_erase_add Finset.univ
    (fun k => (boundedDominantAssignment n z i Q hQ a k).val) (Finset.mem_univ i)
  have ht := Finset.sum_erase_add Finset.univ (boundedTailValue n z i a) (Finset.mem_univ i)
  have hz : boundedTailValue n z i a i = 0 := by simp [boundedTailValue]
  have hi : (boundedDominantAssignment n z i Q hQ a i).val =
      Q - ∑ k, boundedTailValue n z i a k := by simp [boundedDominantAssignment]
  have hs : (∑ k ∈ Finset.univ.erase i, (boundedDominantAssignment n z i Q hQ a k).val) =
      ∑ k ∈ Finset.univ.erase i, boundedTailValue n z i a k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp hk).1
    simp only [boundedDominantAssignment,boundedTailValue,dite_eq_right hki]
  rw [hi,hs] at he
  rw [hz,add_zero] at ht
  omega
#print axioms Paper7MomentCounts.boundedDominantAssignment_sum

def boundedDominantFibreEquiv (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (hQ : Q ≤ z i) (hrest : (∑ k ∈ Finset.univ.erase i, z k) ≤ Q) :
    ((k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) ≃
      {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = Q} where
  toFun a := ⟨boundedDominantAssignment n z i Q hQ a,
    boundedDominantAssignment_sum n z i Q hQ hrest a⟩
  invFun q := fun k => q.val k.val
  left_inv a := by
    funext k
    simp only [boundedDominantAssignment,dite_eq_right k.property]
  right_inv q := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    by_cases hki : k = i
    · subst k
      have ht := Finset.sum_erase_add Finset.univ
        (boundedTailValue n z i (fun j => q.val j.val)) (Finset.mem_univ i)
      have hz : boundedTailValue n z i (fun j => q.val j.val) i = 0 := by simp [boundedTailValue]
      have hs : (∑ k ∈ Finset.univ.erase i, boundedTailValue n z i (fun j => q.val j.val) k) =
          ∑ k ∈ Finset.univ.erase i, (q.val k).val := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [boundedTailValue,dite_eq_right (Finset.mem_erase.mp hk).1]
      have he := Finset.sum_erase_add Finset.univ (fun k => (q.val k).val) (Finset.mem_univ i)
      rw [hz,add_zero,hs] at ht
      rw [q.property] at he
      simp only [boundedDominantAssignment,↓reduceDIte]
      omega
    · simp only [boundedDominantAssignment,dite_eq_right hki]
#print axioms Paper7MomentCounts.boundedDominantFibreEquiv

theorem boundedQDP_dominant_product (n : ℕ) (z : Fin n → ℕ) (i : Fin n) (Q : ℕ)
    (hQ : Q ≤ z i) (hrest : (∑ k ∈ Finset.univ.erase i, z k) ≤ Q) :
    Paper7MomentDP.boundedQDP n z Q = ∏ k : {k : Fin n // k ≠ i}, (z k.val + 1) := by
  classical
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  calc
    Nat.card {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = Q} =
        Nat.card ((k : {k : Fin n // k ≠ i}) → Fin (z k.val + 1)) :=
      Nat.card_congr (boundedDominantFibreEquiv n z i Q hQ hrest).symm
    _ = ∏ k : {k : Fin n // k ≠ i}, (z k.val + 1) := by
      rw [Nat.card_eq_fintype_card,Fintype.card_pi]
      simp only [Fintype.card_fin]
#print axioms Paper7MomentCounts.boundedQDP_dominant_product

end Paper7MomentCounts
