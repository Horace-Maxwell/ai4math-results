import Research.Backfill.Paper7.Lemma22GapBounds
import Research.Backfill.Paper7.Lemma22ExceptionalOffsets

/-! All three maximum bounds using actual support-coordinate injections.
No unproved gap-sum or parity identity is a hypothesis of the final clause. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Scalar arithmetic after the proved empty/nonempty support bounds. -/
theorem offset_maximum_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (r : ℕ)
    (hoff : r + (Kq b q).card = (∑ k, q k) + deltaE b p q ε) :
    r ≤ max (∑ k, q k) 2 := by
  classical
  by_cases hK : Kq b q = ∅
  · have hs : (∑ k, q k) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact Nat.eq_zero_of_not_pos (not_pos_q_of_empty b q hK k)
    have hd := deltaE_empty_bound b p q hb ε hK
    have hc : (Kq b q).card = 0 := by rw [hK]; rfl
    omega
  · have hd := deltaE_nonempty_bound b p q ε (Finset.nonempty_iff_ne_empty.mpr hK)
    have hle : r ≤ ∑ k, q k := by omega
    exact hle.trans (le_max_left _ _)
#print axioms Paper7Lemma22Gaps.offset_maximum_bound

theorem sign_maximum_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    mult (SG b p q) ε ≤ max (∑ k, q k) 2 :=
  offset_maximum_bound b p q hb ε _ (Paper7Lemma22.sign_offset_real b p q hb ε hε)
#print axioms Paper7Lemma22Gaps.sign_maximum_bound

theorem overR_zeroSystem_eq_Wmat (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    overR (zeroSystem b p) = Wmat b (fun _ => 0) p 0 := by
  classical
  apply Matrix.ext
  intro k j
  have hcast : ((cycleAdjZ b k j : ℤ) : ℝ) =
      (SimpleGraph.cycleGraph b).adjMatrix ℝ k j := by
    by_cases h : (SimpleGraph.cycleGraph b).Adj k j <;>
      simp [cycleAdjZ, SimpleGraph.adjMatrix_apply, h]
  by_cases hp : 0 < p k
  · by_cases hj : j = k <;>
      simp [overR, zeroSystem, Wmat, Matrix.map_apply, hp, hj]
  · simp only [overR, Matrix.map_apply, zeroSystem, Wmat, hp, ite_false,
      hcast, Paper7Lemma22.cycle_adjacency_entry b hb, zero_mul, ite_self, sub_zero]
#print axioms Paper7Lemma22Gaps.overR_zeroSystem_eq_Wmat

theorem zero_nullity_eq_deltaE_zero (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    matrixNullity (overQ (zeroSystem b p)) = deltaE b (fun _ => 0) p 0 := by
  have hQR := (Paper7Rank.check_RankReductionAndNullity (Fin b)
    (zeroSystem b p) 2 Nat.prime_two).2.2.2.1
  calc
    matrixNullity (overQ (zeroSystem b p)) =
        matrixNullity (overR (zeroSystem b p)) := hQR
    _ = deltaE b (fun _ => 0) p 0 := by
      rw [overR_zeroSystem_eq_Wmat b p hb]
      rfl
#print axioms Paper7Lemma22Gaps.zero_nullity_eq_deltaE_zero

theorem zero_offset_deltaE (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 + (Kq b p).card =
      (∑ k, p k) + deltaE b (fun _ => 0) p 0 := by
  have h := Paper7Lemma22.zero_offset_reduced b p q hb
  rw [zero_nullity_eq_deltaE_zero b p hb] at h
  exact h
#print axioms Paper7Lemma22Gaps.zero_offset_deltaE

theorem zero_maximum_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 ≤ max (∑ k, p k) 2 :=
  offset_maximum_bound b (fun _ => 0) p hb 0 _ (zero_offset_deltaE b p q hb)
#print axioms Paper7Lemma22Gaps.zero_maximum_bound

/-- The exact final three bounds of frozen Lemma22, with no gap hypotheses. -/
theorem lemma22_maximum_bounds (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 ≤ max (∑ k, p k) 2 ∧
    mult (SG b p q) 1 ≤ max (∑ k, q k) 2 ∧
    mult (SG b p q) (-1) ≤ max (∑ k, q k) 2 :=
  ⟨zero_maximum_bound b p q hb,
    sign_maximum_bound b p q hb 1 (Or.inl rfl),
    sign_maximum_bound b p q hb (-1) (Or.inr rfl)⟩
#print axioms Paper7Lemma22Gaps.lemma22_maximum_bounds

end Paper7Lemma22Gaps
