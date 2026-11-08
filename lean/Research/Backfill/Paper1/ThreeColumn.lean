import Research.Backfill.Paper1.ClosedForms
import Research.ICGEqualParityBMain

/-!
The three parts of the frozen Paper 1 Lemma26, via the exact three rows of T₂
and the existing column surplus estimates. All parameters retain 0 ≤ μ ≤ 1.
The source's compilation and acceptance status is recorded separately.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGEqualParityB

namespace ThreeColumn

lemma rows_two (p : ℝ) (w : ℕ → ℝ) :
    Challenge.tMulVec 2 p w 0 = Mc0 (p - 1) (w 0) (w 1) (w 2) ∧
    Challenge.tMulVec 2 p w 1 = Mc1 (p - 1) (w 0) (w 1) (w 2) ∧
    Challenge.tMulVec 2 p w 2 = Mc2 (p - 1) (w 0) (w 1) (w 2) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    norm_num only [Challenge.tMulVec, Challenge.tEntry, Finset.sum_range_succ,
      Finset.sum_range_zero, Mc0, Mc1, Mc2]
    simp only [true_and, false_and, ite_true, ite_false]
    ring

lemma dNorm_two {p : ℝ} (hp : 2 < p) : Challenge.dNorm 2 p = Dp (p - 1) := by
  rw [ClosedForms.dNorm_eq_dClosed hp]
  norm_num [Challenge.dClosed, Finset.sum_range_succ, Dp]
  ring

lemma psi_eq_Sc {p : ℝ} (hp : 2 < p) (q μ : ℝ) (c ζ : ℕ → ℝ) :
    Challenge.psi 2 p q μ c ζ =
      Sc (p - 1) (q - 1) μ
        (Mc0 (p - 1) (c 0) (c 1) (c 2))
        (Mc1 (p - 1) (c 0) (c 1) (c 2))
        (Mc2 (p - 1) (c 0) (c 1) (c 2))
        (Mc0 (p - 1) (ζ 0) (ζ 1) (ζ 2))
        (Mc1 (p - 1) (ζ 0) (ζ 1) (ζ 2))
        (Mc2 (p - 1) (ζ 0) (ζ 1) (ζ 2)) := by
  obtain ⟨hc0, hc1, hc2⟩ := rows_two p c
  obtain ⟨hz0, hz1, hz2⟩ := rows_two p ζ
  simp [Challenge.psi, Challenge.DeltaC, Challenge.l1, Finset.sum_range_succ,
    dNorm_two hp, Sc, hc0, hc1, hc2, hz0, hz1, hz2, Challenge.hcell, ICGGeneral.hcell]
  ring

lemma pmAlt_of_patterns {c : ℕ → ℝ}
    (h : (c 0 = 1 ∧ c 1 = -1 ∧ c 2 = 1) ∨
      (c 0 = -1 ∧ c 1 = 1 ∧ c 2 = -1)) : Challenge.IsPmAlt 2 c := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · left
    intro i hi
    interval_cases i <;> simp_all [Challenge.sAlt]
  · right
    intro i hi
    interval_cases i <;> simp_all [Challenge.sAlt]

lemma g3_row_data {R : ℝ} (hR : 2 ≤ R) {c : ℕ → ℝ}
    (hc : Challenge.IsPm3 c Challenge.g3) :
    Mc0 R (c 0) (c 1) (c 2) = 0 ∧
    |Mc1 R (c 0) (c 1) (c 2)| = 2 * R * (R + 1) ∧
    |Mc2 R (c 0) (c 1) (c 2)| = R ^ 2 - 1 := by
  have hRR : 0 ≤ 2 * R * (R + 1) := by nlinarith
  have hRs : 0 ≤ R ^ 2 - 1 := by nlinarith
  rcases hc with h | h
  · have h0 : c 0 = 1 := by simpa [Challenge.g3] using h 0 (by norm_num)
    have h1 : c 1 = -1 := by simpa [Challenge.g3] using h 1 (by norm_num)
    have h2 : c 2 = -1 := by simpa [Challenge.g3] using h 2 le_rfl
    simp only [h0, h1, h2]
    obtain ⟨e0, e1, e2⟩ := col_C R
    refine ⟨e0, ?_, ?_⟩
    · rw [e1, abs_neg, abs_of_nonneg hRR]
    · rw [e2, abs_of_nonneg hRs]
  · have h0 : c 0 = -1 := by simpa [Challenge.g3] using h 0 (by norm_num)
    have h1 : c 1 = 1 := by simpa [Challenge.g3] using h 1 (by norm_num)
    have h2 : c 2 = 1 := by simpa [Challenge.g3] using h 2 le_rfl
    simp only [h0, h1, h2]
    obtain ⟨e0, e1, e2⟩ := col_nC R
    refine ⟨e0, ?_, ?_⟩
    · rw [e1, abs_of_nonneg hRR]
    · rw [e2, abs_neg, abs_of_nonneg hRs]

lemma g4_row_data (R : ℝ) {c : ℕ → ℝ}
    (hc : Challenge.IsPm3 c Challenge.g4) :
    Mc0 R (c 0) (c 1) (c 2) = 0 ∧
    Mc1 R (c 0) (c 1) (c 2) = 0 ∧
    |Mc2 R (c 0) (c 1) (c 2)| = (R + 1) ^ 2 := by
  rcases hc with h | h
  · have h0 : c 0 = 1 := by simpa [Challenge.g4] using h 0 (by norm_num)
    have h1 : c 1 = 1 := by simpa [Challenge.g4] using h 1 (by norm_num)
    have h2 : c 2 = 1 := by simpa [Challenge.g4] using h 2 le_rfl
    simp only [h0, h1, h2]
    obtain ⟨e0, e1, e2⟩ := col_E R
    refine ⟨e0, e1, ?_⟩
    rw [e2, abs_of_nonneg (sq_nonneg (R + 1))]
  · have h0 : c 0 = -1 := by simpa [Challenge.g4] using h 0 (by norm_num)
    have h1 : c 1 = -1 := by simpa [Challenge.g4] using h 1 (by norm_num)
    have h2 : c 2 = -1 := by simpa [Challenge.g4] using h 2 le_rfl
    simp only [h0, h1, h2]
    obtain ⟨e0, e1, e2⟩ := col_nE R
    refine ⟨e0, e1, ?_⟩
    rw [e2, abs_neg, abs_of_nonneg (sq_nonneg (R + 1))]

end ThreeColumn

theorem check_Lemma26 : Challenge.Lemma26 := by
  intro p q hpq μ hμ0 hμ1 ζ hζ
  have hPQ : PQok (p - 1) (q - 1) :=
    ParamB.pq (show ParamB p q from hpq)
  obtain ⟨hR, _hQ⟩ := hPQ.two
  have hp : 2 < p := by linarith
  obtain ⟨hB0, hB1, hB2⟩ := Mc_abs_le
    (show 0 ≤ p - 1 by linarith) (hζ 0 (by norm_num))
    (hζ 1 (by norm_num)) (hζ 2 le_rfl)
  obtain ⟨hz0, hz1, _hz2⟩ := ThreeColumn.rows_two p ζ
  refine ⟨?_, ?_, ?_⟩
  · intro c hc hna
    have hnot : ¬ ((c 0 = 1 ∧ c 1 = -1 ∧ c 2 = 1) ∨
        (c 0 = -1 ∧ c 1 = 1 ∧ c 2 = -1)) := by
      intro h
      exact hna (ThreeColumn.pmAlt_of_patterns h)
    have h := lemS hPQ hμ0 hμ1 (hc 0 (by norm_num))
      (hc 1 (by norm_num)) (hc 2 le_rfl) hB0 hB1 hB2
    rw [ThreeColumn.psi_eq_Sc hp]
    exact h.2 hnot
  · intro c hc
    obtain ⟨hc0, hc1, hc2⟩ := ThreeColumn.g3_row_data hR hc
    rw [ThreeColumn.psi_eq_Sc hp, hz0, hc0]
    have h := boundC (B0 := Mc0 (p - 1) (ζ 0) (ζ 1) (ζ 2))
      hPQ hμ0 hμ1 hc1 hc2 hB1 hB2
    nlinarith only [h]
  · intro c hc
    obtain ⟨hc0, hc1, hc2⟩ := ThreeColumn.g4_row_data (p - 1) hc
    rw [ThreeColumn.psi_eq_Sc hp, hz0, hz1, hc0, hc1]
    have h := boundE
      (B0 := Mc0 (p - 1) (ζ 0) (ζ 1) (ζ 2))
      (B1 := Mc1 (p - 1) (ζ 0) (ζ 1) (ζ 2)) hPQ hμ0 hμ1 hc2 hB2
    nlinarith only [h]

#print axioms check_Lemma26
end CodexPaper1
