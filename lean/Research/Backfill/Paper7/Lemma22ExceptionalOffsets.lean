import Research.Backfill.Paper7.ReducedMultiplicityExactness

/-! Real exceptional offsets obtained from the actual integral-matrix reduced
systems. Gap decomposition and the zero-system parity count are separate gaps. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace Paper7Lemma22

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Reduced

theorem cycle_adjacency_entry (b : ℕ) (hb : 3 ≤ b) (k j : Fin b) :
    (SimpleGraph.cycleGraph b).adjMatrix ℝ k j =
      (if j = prv b k then 1 else 0) + (if j = nxt b k then 1 else 0) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  have hne : k - 1 ≠ k + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc k, left_eq_add]
    exact ne_of_beq_false rfl
  have hpne : prv (n + 3) k ≠ nxt (n + 3) k := by
    simpa only [prv, nxt, finRotate_symm_apply, finRotate_apply] using hne
  have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj k j ↔
      j = prv (n + 3) k ∨ j = nxt (n + 3) k := by
    change j ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet k ↔ _
    rw [SimpleGraph.cycleGraph_neighborSet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      prv, nxt, finRotate_symm_apply, finRotate_apply]
  simp only [SimpleGraph.adjMatrix_apply, hadj]
  by_cases hp : j = prv (n + 3) k
  · have hn : j ≠ nxt (n + 3) k := fun h => hpne (hp.symm.trans h)
    rw [ite_eq_left (Or.inl hp), ite_eq_left hp, ite_eq_right hn, add_zero]
  · by_cases hn : j = nxt (n + 3) k
    · rw [ite_eq_left (Or.inr hn), ite_eq_right hp, ite_eq_left hn, zero_add]
    · rw [ite_eq_right (not_or.mpr ⟨hp, hn⟩), ite_eq_right hp, ite_eq_right hn, add_zero]

#print axioms Paper7Lemma22.cycle_adjacency_entry

theorem overR_signSystem (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (ε : ℤ) :
    overR (signSystem b p q ε) = Wmat b p q (ε : ℝ) := by
  classical
  apply Matrix.ext
  intro k j
  have hcast : ((cycleAdjZ b k j : ℤ) : ℝ) =
      (SimpleGraph.cycleGraph b).adjMatrix ℝ k j := by
    by_cases h : (SimpleGraph.cycleGraph b).Adj k j <;>
      simp [cycleAdjZ, SimpleGraph.adjMatrix_apply, h]
  by_cases hq : 0 < q k
  · by_cases hj : j = k <;> simp [overR, signSystem, Wmat, Matrix.map_apply, hq, hj]
  · simp only [overR, Matrix.map_apply, signSystem, Wmat, hq, ite_false,
      Int.cast_add, hcast, cycle_adjacency_entry b hb]
    by_cases hj : j = k <;> simp [hj]
    ring

#print axioms Paper7Lemma22.overR_signSystem

theorem sign_nullity_eq_deltaE (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (ε : ℤ) :
    matrixNullity (overQ (signSystem b p q ε)) = deltaE b p q (ε : ℝ) := by
  have hQR := (Paper7Rank.check_RankReductionAndNullity (Fin b)
    (signSystem b p q ε) 2 Nat.prime_two).2.2.2.1
  calc
    matrixNullity (overQ (signSystem b p q ε)) =
        matrixNullity (overR (signSystem b p q ε)) := hQR
    _ = deltaE b p q (ε : ℝ) := by rw [overR_signSystem b p q hb ε]; rfl

#print axioms Paper7Lemma22.sign_nullity_eq_deltaE

theorem sign_multiplicity_real (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    mult (SG b p q) ε = freeQ b q + deltaE b p q ε := by
  have h (z : ℤ) (hz : z = 1 ∨ z = -1) :
      mult (SG b p q) (z : ℝ) = freeQ b q + deltaE b p q (z : ℝ) := by
    rw [sign_reduced_multiplicity b p q hb z hz, sign_nullity_eq_deltaE b p q hb z]
  rcases hε with rfl | rfl
  · simpa only [Int.cast_one] using h 1 (Or.inl rfl)
  · simpa only [Int.cast_neg, Int.cast_one] using h (-1) (Or.inr rfl)

#print axioms Paper7Lemma22.sign_multiplicity_real

theorem sign_offset_real (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    mult (SG b p q) ε + (Kq b q).card = ∑ k, q k + deltaE b p q ε := by
  rw [sign_multiplicity_real b p q hb ε hε]
  have hf : freeQ b q + (Kq b q).card = ∑ k, q k := freeQ_add_card b q
  omega

#print axioms Paper7Lemma22.sign_offset_real

/-- The exact reduced zero offset; it does not identify its nullity with delta0. -/
theorem zero_offset_reduced (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 + (Kp b p).card =
      ∑ k, p k + matrixNullity (overQ (zeroSystem b p)) := by
  rw [zero_reduced_multiplicity b p q hb]
  have hf : freeP b p + (Kp b p).card = ∑ k, p k := freeP_add_card b p
  omega

#print axioms Paper7Lemma22.zero_offset_reduced

end Paper7Lemma22
