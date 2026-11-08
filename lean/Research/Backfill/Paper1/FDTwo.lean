import Research.Backfill.Paper1.ThreeColumn
import Research.Backfill.Paper1.ColumnIdentity

/-!
Full frozen Lemma29. The strict surplus-sum argument is extracted from the
existing case_B proof before its weaker G < Theta conclusion is formed.
Both fd2a and the p = 3 two-column branch are retained, including b = 2.
The final bridge identifies every frozen psiCol with the old ScY and uses
mu_(b-1) = nu_b. Compilation/acceptance evidence is recorded separately.
-/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral ICGEqualParityB
namespace FDTwo

lemma surplus_sum_strict {p q : ℝ} {b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hPQ : PQok (p - 1) (q - 1)) (hb : Even b) (hb2 : 2 ≤ b)
    (hY : SignMat b Y) (hB : Y 0 b = 1 ∧ Y 1 b = 1 ∧ Y 2 b = -1) :
    4 * (p - 1) * ((q - 1 + 1) * nu q b) < ∑ k ∈ range b, ScY p q b Y k := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hbb : b - 1 + 1 = b := by omega
  have hS := sum_ScY_nonneg hPQ hY (p := p) (q := q)
  have hρrec : (q - 1 + 1) * nu q b = q - 1 - nu q (b - 1) := by
    have := nu_rec' hq0 (b - 1)
    rwa [hbb] at this
  -- the surplus of column `b - 1`
  have hlast : ScY p q b Y (b - 1) = Sc (p - 1) (q - 1) (nu q (b - 1))
      (Mc0 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (Mc1 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (Mc2 (p - 1) (Y 0 (b - 1)) (Y 1 (b - 1)) (Y 2 (b - 1)))
      (-(2 * (p - 1) * (p - 1 + 1))) (-(2 * (p - 1))) ((p - 1) ^ 2 + 2 * (p - 1) - 1) := by
    unfold ScY
    rw [hbb, Zp_self, Zp_self, Zp_self]
    simp only [rw0, rw1, rw2]
    obtain ⟨a0, a1, a2⟩ := hB
    rw [a0, a1, a2]
    obtain ⟨e0, e1, e2⟩ := col_B (p - 1)
    rw [e0, e1, e2]
  have c0 := hY 0 (by norm_num) (b - 1) (by omega)
  have c1 := hY 1 (by norm_num) (b - 1) (by omega)
  have c2 := hY 2 le_rfl (b - 1) (by omega)
  have hμ1 := (nu_bounds hq.le (b - 1)).2
  have hμ0 := nu_nonneg'' hq (b - 1)
  by_cases hcase : ¬ (Y 0 (b - 1) = -1 ∧ Y 1 (b - 1) = -1 ∧ Y 2 (b - 1) = 1) ∨ 4 ≤ p - 1
  · -- FD2 (a)
    have ha := fd2a hPQ hμ0 hμ1 c0 c1 c2 hcase
    rw [← hlast] at ha
    have hsingle : ScY p q b Y (b - 1) ≤ ∑ k ∈ range b, ScY p q b Y k :=
      Finset.single_le_sum hS (mem_range.mpr (by omega))
    rw [hρrec]
    linarith
  · -- FD2 (b): `p = 3` and the chain column at `b - 1`
    push Not at hcase
    obtain ⟨⟨v0, v1, v2⟩, hp4⟩ := hcase
    have hP2 : p - 1 = 2 := by
      rcases hPQ with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · exact h1
    have hQ4 : 4 ≤ q - 1 := by
      rcases hPQ with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · exact h2
    -- column `b - 1`: the chain cost
    have hS1 : 2 * (q - 1) * (1 + nu q (b - 1)) ≤ ScY p q b Y (b - 1) := by
      rw [hlast, v0, v1, v2]
      obtain ⟨e0, e1, e2⟩ := col_nB (p - 1)
      rw [e0, e1, e2]
      have hL := Sc_ge_small (P := p - 1) (Q := q - 1) (μ := nu q (b - 1))
        (A0 := 2 * (p - 1) * (p - 1 + 1)) (A1 := 2 * (p - 1))
        (A2 := -((p - 1) ^ 2 + 2 * (p - 1) - 1)) (B0 := -(2 * (p - 1) * (p - 1 + 1)))
        (B1 := -(2 * (p - 1))) (B2 := (p - 1) ^ 2 + 2 * (p - 1) - 1) hμ0 hμ1 (by linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg (2 * (p - 1) * (p - 1 + 1))); linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg (2 * (p - 1))); linarith)
        (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ q - 1)
              (abs_nonneg ((p - 1) ^ 2 + 2 * (p - 1) - 1)); linarith)
      have hPP : 0 ≤ 2 * (p - 1) * (p - 1 + 1) := by nlinarith
      have hf : 0 ≤ (p - 1) ^ 2 + 2 * (p - 1) - 1 := by nlinarith
      rw [abs_of_nonneg hPP, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (p - 1)), abs_neg,
        abs_of_nonneg hf] at hL
      unfold Dp at hL
      have hval : (q - 1) * (1 + nu q (b - 1)) * (5 * (p - 1) ^ 2 + 2 * (p - 1) + 1 -
          (2 * (p - 1) * (p - 1 + 1) + 2 * (p - 1) + ((p - 1) ^ 2 + 2 * (p - 1) - 1))) =
          2 * (q - 1) * (1 + nu q (b - 1)) := by
        rw [hP2]; ring
      linarith
    -- column `b - 2`: dominance at the state `-μ₀ α(B)`
    have hS2 : 2 * (q - 1) * (1 + nu q (b - 2)) ≤ ScY p q b Y (b - 2) := by
      obtain ⟨s0, s1, s2⟩ := chain_state (p := p) hq (by omega : 1 ≤ b) hB ⟨v0, v1, v2⟩
      have hb2' : b - 2 + 1 = b - 1 := by omega
      unfold ScY
      rw [hb2', s0, s1, s2]
      simp only [rw0, rw1, rw2]
      have hm : (q - 1 + 1) * nu q 1 = q - 1 - 1 := by
        have := nu_rec' hq0 0
        rwa [nu_zero] at this
      exact fd2dom hP2 hQ4 (nu_lo' hq (b - 2)) (nu_bounds hq.le (b - 2)).2 hm
        (hY 0 (by norm_num) (b - 2) (by omega)) (hY 1 (by norm_num) (b - 2) (by omega))
        (hY 2 le_rfl (b - 2) (by omega))
    have hsub : ({b - 2, b - 1} : Finset ℕ) ⊆ range b := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_range]
      omega
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hS j hj)
    rw [Finset.sum_pair (by omega)] at hpair
    have hx : (q - 1 + 1) * nu q (b - 1) = q - 1 - nu q (b - 2) := by
      have := nu_rec' hq0 (b - 2)
      rwa [show b - 2 + 1 = b - 1 by omega] at this
    have hy := nu_gtL' hq (k := b - 2) (by obtain ⟨r, hr⟩ := hb; exact ⟨r - 1, by omega⟩)
    have h2c := two_col hQ4 hx hρrec hy
    rw [hP2]
    nlinarith

lemma psiCol_eq_ScY {p q : ℝ} (hp : 2 < p) (hq : q ≠ 0)
    (b : ℕ) (Y : ℕ → ℕ → ℝ) {j : ℕ} (hj : j < b) :
    Challenge.psiCol 2 b p q Y j = ScY p q b Y j := by
  have hr0 : rw0 p Y = ColumnIdentity.row 2 p Y 0 := by
    funext l
    exact (ThreeColumn.rows_two p (Challenge.col Y l)).1.symm
  have hr1 : rw1 p Y = ColumnIdentity.row 2 p Y 1 := by
    funext l
    exact (ThreeColumn.rows_two p (Challenge.col Y l)).2.1.symm
  have hr2 : rw2 p Y = ColumnIdentity.row 2 p Y 2 := by
    funext l
    exact (ThreeColumn.rows_two p (Challenge.col Y l)).2.2.symm
  have hz0 := ColumnIdentity.Zp_row_eq_zeta hq 2 b p Y 0 (j + 1) hj
  have hz1 := ColumnIdentity.Zp_row_eq_zeta hq 2 b p Y 1 (j + 1) hj
  have hz2 := ColumnIdentity.Zp_row_eq_zeta hq 2 b p Y 2 (j + 1) hj
  have hidx : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
  obtain ⟨hv0, hv1, hv2⟩ := ThreeColumn.rows_two p (Challenge.zetaPath b q Y j)
  rw [← hr0, hidx, hv0] at hz0
  rw [← hr1, hidx, hv1] at hz1
  rw [← hr2, hidx, hv2] at hz2
  unfold Challenge.psiCol
  rw [ThreeColumn.psi_eq_Sc hp, Additional.mu_pred_eq_nu, ← hz0, ← hz1, ← hz2]
  rfl

end FDTwo

theorem check_Lemma29 : Challenge.Lemma29 := by
  intro b hb2 hb p q hreg Y hY hLast
  have hPQ : PQok (p - 1) (q - 1) := ParamB.pq (show ParamB p q from hreg)
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hp : 2 < p := by linarith
  have hq : q ≠ 0 := by linarith
  have hB : Y 0 b = 1 ∧ Y 1 b = 1 ∧ Y 2 b = -1 := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Challenge.g2] using hLast 0 (by norm_num)
    · simpa [Challenge.g2] using hLast 1 (by norm_num)
    · simpa [Challenge.g2] using hLast 2 le_rfl
  have h := FDTwo.surplus_sum_strict hPQ hb hb2 (show SignMat b Y from hY) hB
  have hsum : (∑ j ∈ range b, Challenge.psiCol 2 b p q Y j) =
      ∑ j ∈ range b, ScY p q b Y j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact FDTwo.psiCol_eq_ScY hp hq b Y (Finset.mem_range.mp hj)
  rw [hsum, Additional.mu_pred_eq_nu]
  simpa only [sub_add_cancel, mul_assoc] using h

#print axioms check_Lemma29
end CodexPaper1
