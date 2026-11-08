import Research.Backfill.Paper1.Prop31Selection

/-! Static proof of the full first-deviation (CondF) branch. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31

lemma tMulVec_congr (a : ℕ) (p : ℝ) {c c' : ℕ → ℝ}
    (hc : ∀ i ≤ a, c i = c' i) (u : ℕ) :
    Challenge.tMulVec a p c u = Challenge.tMulVec a p c' u := by
  unfold Challenge.tMulVec
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i (by simpa using Finset.mem_range.mp hi)]

lemma DeltaC_congr (a : ℕ) (p : ℝ) {c c' : ℕ → ℝ}
    (hc : ∀ i ≤ a, c i = c' i) :
    Challenge.DeltaC a p c = Challenge.DeltaC a p c' := by
  unfold Challenge.DeltaC Challenge.l1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [tMulVec_congr a p hc]

lemma psi_congr (a : ℕ) (p q μ : ℝ) {c c' ζ ζ' : ℕ → ℝ}
    (hc : ∀ i ≤ a, c i = c' i) (hζ : ∀ i ≤ a, ζ i = ζ' i) :
    Challenge.psi a p q μ c ζ = Challenge.psi a p q μ c' ζ' := by
  unfold Challenge.psi
  rw [DeltaC_congr a p hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [tMulVec_congr a p hc, tMulVec_congr a p hζ]

lemma psi_sign_scale (a : ℕ) (p q μ : ℝ) (c ζ : ℕ → ℝ) (k : ℕ) :
    Challenge.psi a p q μ (fun i => (-1) ^ k * c i) (fun i => (-1) ^ k * ζ i) =
      Challenge.psi a p q μ c ζ := by
  rcases neg_one_pow_eq_or ℝ k with hs | hs
  · simp only [hs, one_mul]
  · simp only [hs, neg_one_mul]
    unfold Challenge.psi
    have hd : Challenge.DeltaC a p (fun i => -c i) = Challenge.DeltaC a p c := by
      have h := Chain.delta_sign_scale a p 1 (fun i => -c i) c
        (by intros; norm_num)
      exact h
    rw [hd]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hc := Chain.tMulVec_scale_of_eq a p (-1) (fun i => -c i) c
      (by intros; ring) i
    have hz := Chain.tMulVec_scale_of_eq a p (-1) (fun i => -ζ i) ζ
      (by intros; ring) i
    rw [hc, hz]
    simp only [neg_one_mul]
    exact hcell_neg _ _ _ _

lemma sign_scale_isSign {a : ℕ} {c : ℕ → ℝ}
    (hc : Challenge.IsSignVec a c) (k : ℕ) :
    Challenge.IsSignVec a (fun i => (-1) ^ k * c i) := by
  intro i hi
  rcases neg_one_pow_eq_or ℝ k with h | h <;>
    rcases hc i hi with h' | h' <;> simp only [h, h'] <;> norm_num

lemma first_deviation {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) (hpar : b % 2 = a % 2)
    {p q Pm : ℝ} (hreg : Challenge.Regions p q) (hPm : Pm ≤ q - 1)
    (hS : Challenge.CondS a p Pm) (hF : Challenge.CondF a p q)
    {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y)
    {J : ℕ} (hJ : J < b)
    (hdev : ¬ ∀ i ≤ a, Y i J = Challenge.Yminus i J)
    (htail : ∀ l, J < l → l ≤ b → ∀ i ≤ a,
      Y i l = (-1) ^ (l + 1) * Challenge.sAlt i) :
    Challenge.Gval a b p q Y < Challenge.Theta a b p q := by
  obtain ⟨hp, hq, _, hδ, _⟩ := GeneralEquality.region_strict hreg ha
  let c : ℕ → ℝ := fun i => (-1) ^ J * Y i J
  let m := Challenge.mu q ((b : ℤ) - 2 - J)
  have hc : Challenge.IsSignVec a c := sign_scale_isSign (fun i hi => hY i hi J hJ.le) J
  have hna : ¬ ∀ i ≤ a, c i = -Challenge.sAlt i := by
    intro h
    apply hdev
    intro i hi
    have hh := h i hi
    change (-1 : ℝ) ^ J * Y i J = -Challenge.sAlt i at hh
    unfold Challenge.Yminus
    rcases neg_one_pow_eq_or ℝ J with hs | hs
    · change Challenge.sAlt J = 1 at hs
      rw [hs, mul_one]
      change Challenge.sAlt J * Y i J = -Challenge.sAlt i at hh
      simpa only [hs, one_mul] using hh
    · change Challenge.sAlt J = -1 at hs
      rw [hs, mul_neg_one, neg_neg]
      change Challenge.sAlt J * Y i J = -Challenge.sAlt i at hh
      rw [hs, neg_one_mul] at hh
      linarith
  have hstate := (check_Lemma23 a b ha hb hab p q hreg Y hY).2 J hJ htail
  have hpsi : Challenge.psiCol a b p q Y J =
      Challenge.psi a p q (Challenge.mu q ((J : ℤ) - 1)) c
        (fun i => m * Challenge.sAlt i) := by
    unfold Challenge.psiCol
    rw [← psi_sign_scale a p q (Challenge.mu q ((J : ℤ) - 1))
      (Challenge.col Y J) (Challenge.zetaPath b q Y J) J]
    apply psi_congr a p q (Challenge.mu q ((J : ℤ) - 1))
    · intros; rfl
    · intro i hi
      rw [hstate i hi]
      have hs : (-1 : ℝ) ^ J * (-1) ^ J = 1 := by
        exact GeneralEquality.sign_sq J
      change (-1 : ℝ) ^ J * ((-1) ^ J * m * Challenge.sAlt i) = m * Challenge.sAlt i
      calc
        _ = ((-1 : ℝ) ^ J * (-1) ^ J) * (m * Challenge.sAlt i) := by ring
        _ = _ := by rw [hs, one_mul]
  obtain ⟨r, hmem, hr⟩ := FamF_actual hq hb hpar hJ
  have hFval := hF c hc hna
    (Challenge.mu q ((J : ℤ) - 1), m, r) hmem
  have hstrict : 2 * q * Challenge.deltaK a p * Challenge.mu q ((b : ℤ) - 1) <
      Challenge.psiCol a b p q Y J := by
    rw [hpsi]
    have hm := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 2 * q * Challenge.deltaK a p by positivity)
    exact hm.trans_lt hFval
  have hlast := htail b hJ le_rfl
  have halt : Challenge.IsPmAlt a (Challenge.col Y b) := by
    rcases neg_one_pow_eq_or ℝ (b + 1) with hs | hs
    · left; intro i hi; simpa only [Challenge.col, hs, one_mul] using hlast i hi
    · right; intro i hi; simpa only [Challenge.col, hs, neg_one_mul] using hlast i hi
  apply strict_of_surplus hq a b p Y
  rw [OneColumn.delta_pmAlt halt, sub_zero]
  have hle := Finset.single_le_sum
    (fun j hj => (psiCol_nonneg ha hreg hPm hS hY (Finset.mem_range.mp hj)).1)
    (Finset.mem_range.mpr hJ)
  nlinarith

end Prop31
end CodexPaper1
