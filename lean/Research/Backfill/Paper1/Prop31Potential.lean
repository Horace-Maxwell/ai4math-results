import Research.Backfill.Paper1.Prop31Base

/-!
Static source for the scalar-potential and exact interval coverage in
Proposition31. The shifted ν index is used internally; the public conclusions
retain the frozen integer-indexed μ, FamF, Ik and η definitions.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral ICGEqualParity
namespace Prop31

lemma nu_lower {q : ℝ} (hq : 2 < q) (n : ℕ) :
    Challenge.mu q 0 ≤ nu q n := by
  have hm0 : Challenge.mu q 0 = nu q 1 := by
    simpa using Additional.mu_nat_eq_nu q 0
  rw [hm0]
  have he : nu q 1 = (q - 2) / q := by rw [nu_succ, nu_zero]; ring
  rw [he]
  exact (nu_bounds hq.le n).1

lemma nu_low_interval {q : ℝ} (hq : 2 < q) {n : ℕ} (hn : Odd n) :
    Challenge.mu q 0 ≤ nu q n ∧ nu q n ≤ Challenge.muInf q := by
  exact ⟨nu_lower hq n, (nu_odd_lt (by linarith) hn).le⟩

lemma nu_high_interval {q : ℝ} (hq : 2 < q) {n : ℕ}
    (hn : Even n) (hn0 : 0 < n) :
    Challenge.muInf q ≤ nu q n ∧ nu q n ≤ Challenge.mu q 1 := by
  refine ⟨(nu_even_gt (by linarith) hn).le, ?_⟩
  have hm1 : Challenge.mu q 1 = nu q 2 := by
    simpa using Additional.mu_nat_eq_nu q 1
  rw [hm1]
  exact nu_even_le_two (by linarith) hn (by obtain ⟨k, hk⟩ := hn; omega)

lemma nu_even_antitone {q : ℝ} (hq : 2 < q) {m n : ℕ}
    (hm : Even m) (hn : Even n) (hmn : m ≤ n) : nu q n ≤ nu q m := by
  have hq0 : 0 < q := by linarith
  have h1 := nu_sub_L hq0 m
  have h2 := nu_sub_L hq0 n
  have hL : 0 < 1 - (q - 1) / (q + 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hm' : (-1 / q) ^ m = (1 / q) ^ m := by rw [neg_div, hm.neg_pow]
  have hn' : (-1 / q) ^ n = (1 / q) ^ n := by rw [neg_div, hn.neg_pow]
  have hpow : (1 / q) ^ n ≤ (1 / q) ^ m := by
    apply pow_le_pow_of_le_one (by positivity) _ hmn
    rw [div_le_one hq0]; linarith
  rw [hm'] at h1
  rw [hn'] at h2
  nlinarith

lemma eta_nu (q : ℝ) (m n : ℕ) : Challenge.etaMap q n (nu q m) = nu q (m + n) := by
  induction n with
  | zero => simp [Challenge.etaMap]
  | succ n ih => simp only [Challenge.etaMap, ih, Nat.add_succ, nu_succ]

lemma mu_tail_eq_nu (q : ℝ) {b J : ℕ} (hJ : J < b) :
    Challenge.mu q ((b : ℤ) - 2 - J) = nu q (b - (J + 1)) := by
  have he : (b : ℤ) - 2 - J = ((b - (J + 1) : ℕ) : ℤ) - 1 := by omega
  rw [he, Additional.mu_pred_eq_nu]

lemma Ik_actual {q : ℝ} (hq : 2 < q) {a b k : ℕ}
    (hpar : b % 2 = a % 2) (hk : k < b) :
    Challenge.Ik a k q (Challenge.mu q ((b : ℤ) - 2 - k)) := by
  rw [mu_tail_eq_nu q hk]
  unfold Challenge.Ik
  by_cases he : k % 2 = a % 2
  · rw [ite_eq_left he]
    apply nu_low_interval hq
    rw [Nat.odd_iff]
    omega
  · rw [ite_eq_right he]
    by_cases hzero : b - (k + 1) = 0
    · right; rw [hzero, nu_zero]
    · left
      apply nu_high_interval hq
      · rw [Nat.even_iff]; omega
      · omega

lemma C2_interval_actual {q : ℝ} (hq : 2 < q) {a b : ℕ}
    (hpar : b % 2 = a % 2) (hb : 6 ≤ b) :
    if Even a then Challenge.mu q 0 ≤ Challenge.mu q ((b : ℤ) - 6) ∧
      Challenge.mu q ((b : ℤ) - 6) ≤ Challenge.muInf q
    else Challenge.muInf q ≤ Challenge.mu q ((b : ℤ) - 6) ∧
      Challenge.mu q ((b : ℤ) - 6) ≤ Challenge.mu q 1 := by
  have he : (b : ℤ) - 6 = ((b - 5 : ℕ) : ℤ) - 1 := by omega
  rw [he, Additional.mu_pred_eq_nu]
  split_ifs with ha
  · apply nu_low_interval hq
    have ham := Nat.even_iff.mp ha
    rw [Nat.odd_iff]; omega
  · apply nu_high_interval hq
    · have ham : a % 2 ≠ 0 := by simpa only [Nat.even_iff] using ha
      rw [Nat.even_iff]; omega
    · omega

lemma FamF_actual {q : ℝ} (hq : 2 < q) {a b J : ℕ}
    (hb : 1 ≤ b) (hpar : b % 2 = a % 2) (hJ : J < b) :
    ∃ r : ℝ, Challenge.FamF a q
      (Challenge.mu q ((J : ℤ) - 1), Challenge.mu q ((b : ℤ) - 2 - J), r) ∧
      Challenge.mu q ((b : ℤ) - 1) ≤ r := by
  rw [Additional.mu_pred_eq_nu, mu_tail_eq_nu q hJ, Additional.mu_pred_eq_nu]
  by_cases ha : Even a
  · have hbE : Even b := by rw [Nat.even_iff]; rw [hpar]; exact Nat.even_iff.mp ha
    have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbE; omega
    have hbmod := Nat.even_iff.mp hbE
    have hrec : nu q b = (q - 1 - nu q (b - 1)) / q := by
      rw [← nu_succ, Nat.sub_add_cancel hb]
    by_cases hzero : J = 0
    · subst J
      refine ⟨nu q b, ?_, le_rfl⟩
      have hm := nu_low_interval hq (n := b - 1) (by rw [Nat.odd_iff]; omega)
      simp only [Challenge.FamF, ite_eq_left ha, nu_zero, Nat.zero_add]
      exact Or.inl ⟨True.intro, hm.1, hm.2, hrec⟩
    · by_cases hlast : J = b - 1
      · subst J
        refine ⟨nu q b, ?_, le_rfl⟩
        have hm := nu_low_interval hq (n := b - 1) (by rw [Nat.odd_iff]; omega)
        simp only [Challenge.FamF, ite_eq_left ha,
          show b - (b - 1 + 1) = 0 by omega, nu_zero]
        exact Or.inr (Or.inl ⟨True.intro, hm.1, hm.2, hrec⟩)
      · by_cases hJE : Even J
        · refine ⟨nu q J, ?_, nu_even_antitone hq hJE hbE hJ.le⟩
          have hu := nu_high_interval hq hJE (by omega)
          have hm := nu_low_interval hq (n := b - (J + 1))
            (by rw [Nat.odd_iff]; have := Nat.even_iff.mp hJE; have := Nat.even_iff.mp hbE; omega)
          simp only [Challenge.FamF, ite_eq_left ha]
          exact Or.inr (Or.inr (Or.inl ⟨hu.1, hu.2, hm.1, hm.2, True.intro⟩))
        · have hmE : Even (b - (J + 1)) := by
            have hh : J % 2 ≠ 0 := by simpa only [Nat.even_iff] using hJE
            have := Nat.even_iff.mp hbE
            rw [Nat.even_iff]; omega
          refine ⟨nu q (b - (J + 1)), ?_,
            nu_even_antitone hq hmE hbE (Nat.sub_le _ _)⟩
          have hu := nu_low_interval hq (Nat.not_even_iff_odd.mp hJE)
          have hm := nu_high_interval hq hmE (by omega)
          simp only [Challenge.FamF, ite_eq_left ha]
          exact Or.inr (Or.inr (Or.inr ⟨hu.1, hu.2, hm.1, hm.2, True.intro⟩))
  · have hbO : Odd b := by
      rw [Nat.odd_iff]
      have ham : a % 2 ≠ 0 := by simpa only [Nat.even_iff] using ha
      omega
    by_cases hb1 : b = 1
    · subst b
      have hJ0 : J = 0 := by omega
      subst J
      refine ⟨nu q 1, ?_, le_rfl⟩
      simp only [Challenge.FamF, ite_eq_right ha, nu_zero, Nat.zero_add, Nat.sub_self]
      exact Or.inl ⟨True.intro, True.intro, (by simpa using (Additional.mu_nat_eq_nu q 0).symm)⟩
    · have hb3 : 3 ≤ b := by have := Nat.odd_iff.mp hbO; omega
      have hrec : nu q b = (q - 1 - nu q (b - 1)) / q := by
        rw [← nu_succ, Nat.sub_add_cancel hb]
      by_cases hzero : J = 0
      · subst J
        refine ⟨nu q b, ?_, le_rfl⟩
        have hm := nu_high_interval hq (n := b - 1)
          (by rw [Nat.even_iff]; have := Nat.odd_iff.mp hbO; omega) (by omega)
        simp only [Challenge.FamF, ite_eq_right ha, nu_zero, Nat.zero_add]
        exact Or.inr (Or.inl ⟨True.intro, hm.1, hm.2, hrec⟩)
      · by_cases hlast : J = b - 1
        · subst J
          refine ⟨nu q b, ?_, le_rfl⟩
          have hu := nu_high_interval hq (n := b - 1)
            (by rw [Nat.even_iff]; have := Nat.odd_iff.mp hbO; omega) (by omega)
          simp only [Challenge.FamF, ite_eq_right ha,
            show b - (b - 1 + 1) = 0 by omega, nu_zero]
          exact Or.inr (Or.inr (Or.inl ⟨True.intro, hu.1, hu.2, hrec⟩))
        · refine ⟨Challenge.muInf q, ?_, (nu_odd_lt (by linarith) hbO).le⟩
          simp only [Challenge.FamF, ite_eq_right ha]
          apply Or.inr; apply Or.inr; apply Or.inr
          refine ⟨?_, True.intro⟩
          by_cases hJE : Even J
          · right
            have hu := nu_high_interval hq hJE (by omega)
            have hm := nu_high_interval hq (n := b - (J + 1))
              (by rw [Nat.even_iff]; have := Nat.even_iff.mp hJE; have := Nat.odd_iff.mp hbO; omega)
              (by omega)
            exact ⟨hu.1, hu.2, hm.1, hm.2⟩
          · left
            have hu := nu_low_interval hq (Nat.not_even_iff_odd.mp hJE)
            have hm := nu_low_interval hq (n := b - (J + 1))
              (by rw [Nat.odd_iff]; have hh : J % 2 ≠ 0 := by simpa only [Nat.even_iff] using hJE
                  have := Nat.odd_iff.mp hbO; omega)
            exact ⟨hu.1, hu.2, hm.1, hm.2⟩

end Prop31
end CodexPaper1
