import Research.Backfill.Paper7.B4ThreePSpectralRank

/-! Source-only extraction from the actual simple positive spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem simple_positive_card_lt_four (p q : Fin 4 → ℕ)
    (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q))
    (hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1) :
    (Bplus (SG 4 p q)).card < 4 := by
  have hints : ∀ x ∈ Bplus (SG 4 p q), 2 ≤ x ∧ ∃ z : ℤ, x = z := by
    intro x hx
    obtain ⟨hmem,hx2⟩ := Multiset.mem_filter.mp hx
    exact ⟨hx2,Paper7Moments.integral_spec_entry _ hG x hmem⟩
  have hfloor := integral_square_floor_twenty_five (Bplus (SG 4 p q)) hints
  have hcount (x : ℝ) (hx : 2 ≤ x) : (Bplus (SG 4 p q)).count x ≤ 1 := by
    simpa only [Bplus,mult,Multiset.count_filter,hx,ite_true] using hm x hx
  have h2 : ((Bplus (SG 4 p q)).count 2 : ℝ) ≤ 1 := by exact_mod_cast hcount 2 (by norm_num)
  have h3 : ((Bplus (SG 4 p q)).count 3 : ℝ) ≤ 1 := by exact_mod_cast hcount 3 (by norm_num)
  have h4 : ((Bplus (SG 4 p q)).count 4 : ℝ) ≤ 1 := by exact_mod_cast hcount 4 (by norm_num)
  have hS := (Paper7Counting.lemma42_bounds 4 p q (by decide) (by decide) hG).1
  have hnR : (nOf 4 p q : ℝ) ≤ 49 := by exact_mod_cast hn
  change 25*((Bplus (SG 4 p q)).card : ℝ) ≤ S2 (SG 4 p q)+
    21*((Bplus (SG 4 p q)).count 2 : ℝ)+16*((Bplus (SG 4 p q)).count 3 : ℝ)+
    9*((Bplus (SG 4 p q)).count 4 : ℝ) at hfloor
  have hcR : ((Bplus (SG 4 p q)).card : ℝ) < 4 := by linarith
  exact_mod_cast hcR
#print axioms Paper7B4Analytic.simple_positive_card_lt_four

theorem simple_positive_three_integer_roots (p q : Fin 4 → ℕ)
    (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q))
    (hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1)
    (hcard : (Bplus (SG 4 p q)).card = 3) :
    ∃ r s t : ℕ, 2 ≤ r ∧ r < s ∧ s < t ∧ r^2+s^2+t^2 ≤ 49 ∧
      (r : ℝ) ∈ spec (SG 4 p q) ∧ (s : ℝ) ∈ spec (SG 4 p q) ∧
      (t : ℝ) ∈ spec (SG 4 p q) := by
  obtain ⟨x,y,z,hs⟩ := Multiset.card_eq_three.mp hcard
  have hx : x ∈ Bplus (SG 4 p q) := by rw [hs]; simp
  have hy : y ∈ Bplus (SG 4 p q) := by rw [hs]; simp
  have hz : z ∈ Bplus (SG 4 p q) := by rw [hs]; simp
  obtain ⟨hxm,hx2⟩ := Multiset.mem_filter.mp hx
  obtain ⟨hym,hy2⟩ := Multiset.mem_filter.mp hy
  obtain ⟨hzm,hz2⟩ := Multiset.mem_filter.mp hz
  obtain ⟨X,hX⟩ := Paper7Moments.integral_spec_entry _ hG x hxm
  obtain ⟨Y,hY⟩ := Paper7Moments.integral_spec_entry _ hG y hym
  obtain ⟨Z,hZ⟩ := Paper7Moments.integral_spec_entry _ hG z hzm
  have hX2 : (2 : ℤ) ≤ X := by rw [hX] at hx2; exact_mod_cast hx2
  have hY2 : (2 : ℤ) ≤ Y := by rw [hY] at hy2; exact_mod_cast hy2
  have hZ2 : (2 : ℤ) ≤ Z := by rw [hZ] at hz2; exact_mod_cast hz2
  have hXn : (X.toNat : ℝ) = x := by
    have hh : (X.toNat : ℤ) = X := Int.toNat_of_nonneg (by omega)
    have hc : (X.toNat : ℝ) = (X : ℝ) := by exact_mod_cast hh
    exact hc.trans hX.symm
  have hYn : (Y.toNat : ℝ) = y := by
    have hh : (Y.toNat : ℤ) = Y := Int.toNat_of_nonneg (by omega)
    have hc : (Y.toNat : ℝ) = (Y : ℝ) := by exact_mod_cast hh
    exact hc.trans hY.symm
  have hZn : (Z.toNat : ℝ) = z := by
    have hh : (Z.toNat : ℤ) = Z := Int.toNat_of_nonneg (by omega)
    have hc : (Z.toNat : ℝ) = (Z : ℝ) := by exact_mod_cast hh
    exact hc.trans hZ.symm
  have hXn2 : 2 ≤ X.toNat := by omega
  have hYn2 : 2 ≤ Y.toNat := by omega
  have hZn2 : 2 ≤ Z.toNat := by omega
  have hnodup : (Bplus (SG 4 p q)).Nodup := by
    apply Multiset.nodup_iff_count_le_one.mpr
    intro w
    by_cases hw : 2 ≤ w
    · simpa only [Bplus,mult,Multiset.count_filter,hw,ite_true] using hm w hw
    · simp [Bplus,hw]
  rw [hs] at hnodup
  have hdistinct : x ≠ y ∧ x ≠ z ∧ y ≠ z := by simpa [and_assoc] using hnodup
  have hXY : X.toNat ≠ Y.toNat := by
    intro hh; apply hdistinct.1; rw [← hXn,← hYn,hh]
  have hXZ : X.toNat ≠ Z.toNat := by
    intro hh; apply hdistinct.2.1; rw [← hXn,← hZn,hh]
  have hYZ : Y.toNat ≠ Z.toNat := by
    intro hh; apply hdistinct.2.2; rw [← hYn,← hZn,hh]
  have hsumR : x^2+y^2+z^2 ≤ 49 := by
    have hS := (Paper7Counting.lemma42_bounds 4 p q (by decide) (by decide) hG).1
    have hnr : (nOf 4 p q : ℝ) ≤ 49 := by exact_mod_cast hn
    have he : S2 (SG 4 p q) = x^2+y^2+z^2 := by simp [S2,hs]; ring
    rw [he] at hS
    linarith
  have hsum : X.toNat^2+Y.toNat^2+Z.toNat^2 ≤ 49 := by
    have hh : (X.toNat : ℝ)^2+(Y.toNat : ℝ)^2+(Z.toNat : ℝ)^2 ≤ 49 := by
      rw [hXn,hYn,hZn]; exact hsumR
    exact_mod_cast hh
  have hXm : (X.toNat : ℝ) ∈ spec (SG 4 p q) := by rw [hXn]; exact hxm
  have hYm : (Y.toNat : ℝ) ∈ spec (SG 4 p q) := by rw [hYn]; exact hym
  have hZm : (Z.toNat : ℝ) ∈ spec (SG 4 p q) := by rw [hZn]; exact hzm
  rcases le_total X.toNat Y.toNat with hxy | hyx
  · rcases le_total Y.toNat Z.toNat with hyz | hzy
    · exact ⟨X.toNat,Y.toNat,Z.toNat,hXn2,by omega,by omega,hsum,hXm,hYm,hZm⟩
    · rcases le_total X.toNat Z.toNat with hxz | hzx
      · exact ⟨X.toNat,Z.toNat,Y.toNat,hXn2,by omega,by omega,by omega,hXm,hZm,hYm⟩
      · exact ⟨Z.toNat,X.toNat,Y.toNat,hZn2,by omega,by omega,by omega,hZm,hXm,hYm⟩
  · rcases le_total X.toNat Z.toNat with hxz | hzx
    · exact ⟨Y.toNat,X.toNat,Z.toNat,hYn2,by omega,by omega,by omega,hYm,hXm,hZm⟩
    · rcases le_total Y.toNat Z.toNat with hyz | hzy
      · exact ⟨Y.toNat,Z.toNat,X.toNat,hYn2,by omega,by omega,by omega,hYm,hZm,hXm⟩
      · exact ⟨Z.toNat,Y.toNat,X.toNat,hZn2,by omega,by omega,by omega,hZm,hYm,hXm⟩
#print axioms Paper7B4Analytic.simple_positive_three_integer_roots

end Paper7B4Analytic
