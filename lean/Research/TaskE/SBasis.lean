import Research.TaskE.ChallengeS
import Research.Backfill.Paper1.PathCoordinates
import Research.Backfill.Paper1.TransformRows

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.SProof
open Finset BackfillPaper1.Challenge

lemma entry_negative {a i : ℕ} (hi : i < a) (p : ℝ) :
    tEntry a p i (a - 1 - i) = -(p ^ (a - 1) * (p - 1)) := by
  have hj : a - 1 - i < a := by omega
  have hsum : i + (a - 1 - i) + 1 = a := by omega
  have hnot : ¬ i + (a - 1 - i) + 2 ≤ a := by omega
  unfold tEntry
  rw [ite_eq_left (show i < a ∧ a - 1 - i < a from ⟨hi, hj⟩),
    ite_eq_right hnot, ite_eq_left hsum]

lemma entry_off_nonneg {a i j : ℕ} {p : ℝ} (hp : 3 ≤ p) (hi : i < a)
    (hne : j ≠ a - 1 - i) : 0 ≤ tEntry a p i j := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  unfold tEntry
  split_ifs <;> first | positivity | omega

lemma entry_last_nonneg {a j : ℕ} {p : ℝ} (hp : 3 ≤ p) :
    0 ≤ tEntry a p a j := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  simp only [tEntry, lt_self_iff_false, false_and, ↓reduceIte]
  split_ifs <;> positivity

lemma row_abs_mass : CodexPaper1.TaskE.Challenge.RowAbsMass := by
  classical
  intro a ha p hp i hi
  have hrows := (CodexPaper1.check_TransformRows p (by linarith) a ha).2
  by_cases hia : i = a
  · subst i
    rw [ite_eq_left rfl]
    unfold rowAbsSum
    calc
      _ = ∑ j ∈ range (a + 1), tEntry a p a j := by
        apply sum_congr rfl
        intro j _hj
        exact abs_of_nonneg (entry_last_nonneg hp)
      _ = p ^ a := by simpa [tMulVec] using hrows a le_rfl
  · have hilt : i < a := lt_of_le_of_ne hi hia
    rw [ite_eq_right hia]
    let j := a - 1 - i
    have hj : j ∈ range (a + 1) := mem_range.mpr (by dsimp [j]; omega)
    have hn := entry_negative hilt p
    change tEntry a p i j = -(p ^ (a - 1) * (p - 1)) at hn
    have hL : 0 ≤ p ^ (a - 1) * (p - 1) :=
      mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
    have hnn : tEntry a p i j ≤ 0 := by rw [hn]; exact neg_nonpos.mpr hL
    have he : ∀ k ∈ range (a + 1), |tEntry a p i k| =
        tEntry a p i k - (if k = j then 2 * tEntry a p i j else 0) := by
      intro k _hk
      by_cases hkj : k = j
      · subst k
        rw [ite_eq_left rfl, abs_of_nonpos hnn]
        ring
      · rw [ite_eq_right hkj, sub_zero]
        exact abs_of_nonneg (entry_off_nonneg hp hilt hkj)
    have hsum : (∑ k ∈ range (a + 1), tEntry a p i k) = 0 := by
      simpa only [tMulVec, mul_one, ite_eq_right hia] using hrows i hi
    unfold rowAbsSum
    calc
      _ = ∑ k ∈ range (a + 1),
          (tEntry a p i k - (if k = j then 2 * tEntry a p i j else 0)) :=
        sum_congr rfl he
      _ = _ := by
        rw [sum_sub_distrib, hsum]
        simp only [sum_ite_eq', ite_eq_left hj]
        rw [hn]
        ring

lemma row_path {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) {p : ℝ} (hp : 3 ≤ p)
    (c : ℕ → ℝ) :
    tMulVec a p c (a - 1 - j) =
      p ^ (a - 1) * (p - 1) * (z p a c (j : ℤ) - c j) := by
  have h := (CodexPaper1.check_PathCoordinates p (by linarith) a ha c).2
    (a - 1 - j) (by omega)
  have hi : a - 1 - (a - 1 - j) = j := by omega
  have hz : (a : ℤ) - 1 - ((a - 1 - j : ℕ) : ℤ) = (j : ℤ) := by omega
  simpa only [hi, hz] using h

lemma path_bounds {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    0 < c (j + 1) * z p a c (j : ℤ) ∧
    (p - 2) / p ≤ |z p a c (j : ℤ)| ∧ |z p a c (j : ℤ)| ≤ 1 := by
  have h := (CodexPaper1.check_Lemma8 p (by linarith) a ha c hc).1 (j + 1) (by omega)
  have hz : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
  simpa only [hz] using h

lemma terminal_lower {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    p ^ (a - 1) * (p - 2) ≤ |tMulVec a p c a| := by
  have hp0 : 0 < p := by linarith
  have hz := (CodexPaper1.check_Lemma8 p (by linarith) a ha c hc).1 0 (by omega)
  have hb : (p - 2) / p ≤ |z p a c (-1)| := by simpa using hz.2.1
  have ht := (CodexPaper1.check_PathCoordinates p (by linarith) a ha c).1
  rw [ht, abs_mul, abs_of_pos (pow_pos hp0 a)]
  have hw : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  calc
    _ = p ^ a * ((p - 2) / p) := by rw [hw]; field_simp [hp0.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (pow_pos hp0 a).le

lemma deficit_identity {a : ℕ} {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    DeltaC a p c = 2 * p ^ a * (∑ j ∈ NA a c, mu p (j : ℤ) * |z p a c (j : ℤ)|) := by
  have hx : 2 < p := by linarith
  have hcg : ICGGeneral.IsSign a c := hc
  unfold DeltaC
  rw [Additional.dNorm_eq_L1, Additional.l1_tMulVec_eq_L1,
    ICGGeneral.L1_sgnv hx a, ICGGeneral.L1_sign hx hcg,
    Additional.slack_eq_two_sigma (by linarith : p ≠ 0) a c]
  ring

lemma deficit_pos {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hna : ¬ IsPmAlt a c) : 0 < DeltaC a p c := by
  have h := CodexPaper1.check_Lemma8 p (by linarith) a ha c hc
  rcases lt_or_eq_of_le h.2.2.1 with hh | hh
  · exact sub_pos.mpr hh
  · exact False.elim (hna (h.2.2.2.1.mp hh))

lemma mu_lower {p : ℝ} (hp : 3 ≤ p) (j : ℕ) :
    (p - 2) / p ≤ mu p (j : ℤ) := by
  rw [Additional.mu_nat_eq_nu]
  exact (ICGGeneral.nu_bounds (by linarith : 2 ≤ p) (j + 1)).1

end CodexPaper1.TaskE.SProof
#print axioms CodexPaper1.TaskE.SProof.row_abs_mass
#print axioms CodexPaper1.TaskE.SProof.row_path
#print axioms CodexPaper1.TaskE.SProof.path_bounds
#print axioms CodexPaper1.TaskE.SProof.terminal_lower
#print axioms CodexPaper1.TaskE.SProof.deficit_identity
#print axioms CodexPaper1.TaskE.SProof.deficit_pos
#print axioms CodexPaper1.TaskE.SProof.mu_lower
