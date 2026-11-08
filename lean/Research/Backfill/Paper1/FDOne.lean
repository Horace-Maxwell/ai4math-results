import Research.Backfill.Paper1.ThreeColumn

/-!
The full frozen Lemma28, including the actual integer-indexed potentials.
The existing parameterized fd1 is instantiated at J, b-(J+1), and b;
its endpoint regimes are supplied explicitly. Compilation and acceptance
status is recorded separately from this source.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGEqualParityB ICGGeneral
namespace FDOne

lemma deltaK_two {p : ℝ} (hp : 2 < p) :
    Challenge.deltaK 2 p = (p - 1) ^ 2 + 1 := by
  unfold Challenge.deltaK
  apply (div_eq_iff (by linarith : p + 1 ≠ 0)).2
  norm_num
  ring

/-- The integer potential index may be -1 at the last column. -/
lemma mu_tail_eq (q : ℝ) (b J : ℕ) (hJ : J < b) :
    Challenge.mu q ((b : ℤ) - 2 - J) = nu q (b - (J + 1)) := by
  have h : (b : ℤ) - 2 - J = ((b - (J + 1) : ℕ) : ℤ) - 1 := by omega
  rw [h, Additional.mu_pred_eq_nu]

lemma alt_state_rows (p m : ℝ) :
    Mc0 (p - 1) (m * Challenge.sAlt 0) (m * Challenge.sAlt 1)
        (m * Challenge.sAlt 2) = m * (2 * (p - 1) * (p - 1 + 1)) ∧
    Mc1 (p - 1) (m * Challenge.sAlt 0) (m * Challenge.sAlt 1)
        (m * Challenge.sAlt 2) = m * (-(2 * (p - 1) ^ 2)) ∧
    Mc2 (p - 1) (m * Challenge.sAlt 0) (m * Challenge.sAlt 1)
        (m * Challenge.sAlt 2) = m * ((p - 1) ^ 2 + 1) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    norm_num [Mc0, Mc1, Mc2, Challenge.sAlt]
    ring

lemma psi_alt_state {p : ℝ} (hp : 2 < p) (q μ m : ℝ) (c : ℕ → ℝ) :
    Challenge.psi 2 p q μ c (fun i => m * Challenge.sAlt i) =
      Sc (p - 1) (q - 1) μ
        (Mc0 (p - 1) (c 0) (c 1) (c 2))
        (Mc1 (p - 1) (c 0) (c 1) (c 2))
        (Mc2 (p - 1) (c 0) (c 1) (c 2))
        (m * (2 * (p - 1) * (p - 1 + 1)))
        (m * (-(2 * (p - 1) ^ 2))) (m * ((p - 1) ^ 2 + 1)) := by
  obtain ⟨h0, h1, h2⟩ := alt_state_rows p m
  rw [ThreeColumn.psi_eq_Sc hp, h0, h1, h2]

/-- The three parameter regimes cover both endpoints and every interior J. -/
lemma actual_regime {q : ℝ} (hq : 2 < q) {b J : ℕ} (hb : 2 ≤ b) (hJ : J < b) :
    (nu q J = 1 ∧ (q - 1 + 1) * nu q b = q - 1 - nu q (b - (J + 1))) ∨
    (nu q (b - (J + 1)) = 1 ∧ (q - 1 + 1) * nu q b = q - 1 - nu q J) ∨
    (q - 1 + 1) ^ 2 * nu q (b - (J + 1)) ≤ (q - 1) ^ 2 + 1 := by
  have hq0 : 0 < q := by linarith
  rcases Nat.eq_zero_or_pos J with h0 | h0
  · left
    subst h0
    refine ⟨nu_zero q, ?_⟩
    have h := nu_rec' hq0 (b - 1)
    rw [show b - 1 + 1 = b by omega] at h
    simpa using h
  · by_cases hJb : J = b - 1
    · right
      left
      subst hJb
      refine ⟨by rw [show b - (b - 1 + 1) = 0 by omega, nu_zero], ?_⟩
      have h := nu_rec' hq0 (b - 1)
      rw [show b - 1 + 1 = b by omega] at h
      exact h
    · right
      right
      exact nu_hi' hq (by omega)

end FDOne

theorem check_Lemma28 : Challenge.Lemma28 := by
  intro b hb _heven p q hpq J hJ c hc hna
  have hPQ : PQok (p - 1) (q - 1) :=
    ParamB.pq (show ParamB p q from hpq)
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hp : 2 < p := by linarith
  have hq : 2 < q := by linarith
  have hμ0 := nu_lo' hq J
  have hμ1 := (nu_bounds hq.le J).2
  have hm0 := nu_lo' hq (b - (J + 1))
  have hm1 := (nu_bounds hq.le (b - (J + 1))).2
  have hρ := nu_hi' hq (k := b) (by omega)
  have hreg := FDOne.actual_regime hq hb hJ
  have hnot : ¬ (c 0 = -1 ∧ c 1 = 1 ∧ c 2 = -1) := by
    rintro ⟨h0, h1, h2⟩
    apply hna
    intro i hi
    interval_cases i <;> norm_num [Challenge.sAlt, h0, h1, h2]
  have h := fd1 hPQ hμ0 hμ1 hm0 hm1 hρ hreg
    (hc 0 (by norm_num)) (hc 1 (by norm_num)) (hc 2 le_rfl) hnot
  rw [Additional.mu_pred_eq_nu q J, FDOne.mu_tail_eq q b J hJ,
    FDOne.psi_alt_state hp, FDOne.deltaK_two hp, Additional.mu_pred_eq_nu q b]
  simpa only [sub_add_cancel] using h

#print axioms check_Lemma28
end CodexPaper1
