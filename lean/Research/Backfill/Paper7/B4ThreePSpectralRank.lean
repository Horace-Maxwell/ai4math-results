import Research.Backfill.Paper7.B4ThreePUnitExclusion
import Research.Backfill.Paper7.B4QzeroFullSupport

/-! Source-only exact positive spectral rank and ordered integer roots for
three positive q=0 sites. All root bounds come from the actual spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_positive_delta_zero (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0) :
    (Kp 4 p).card = 3 ∧ delta0 4 p = 1 := by
  have hK : Kp 4 p = {0,1,2} := by
    ext i
    fin_cases i <;> simp [Kp,hp0,hp1,hp2,hp3]
  refine ⟨by rw [hK]; decide,?_⟩
  rw [delta0,hK]
  decide +kernel
#print axioms Paper7B4Analytic.three_positive_delta_zero

theorem three_positive_big_card (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    (Bplus (SG 4 p (fun _ => 0))).card = 3 := by
  have hunit : 1 ∉ spec (SG 4 p (fun _ => 0)) := by
    intro hh
    exact three_p_unit_nonintegral p hp0 hp1 hp2 hp3 hh hG
  have hm1 : mult (SG 4 p (fun _ => 0)) 1 = 0 := Multiset.count_eq_zero.mpr hunit
  obtain ⟨hK,hd⟩ := three_positive_delta_zero p hp0 hp1 hp2 hp3
  have hzero := (Paper7Lemma22.check_Lemma22 4 p (fun _ => 0) (by decide)).2.1
  rw [hK,hd] at hzero
  have he := Paper7Admissible.lemma24_counting_even 4 p (fun _ => 0)
    (by decide) hG (by decide)
  have hc := Paper7Counting.symmetric_spectrum_card (SG 4 p (fun _ => 0)) hG he.1
  change order 4 (pq 4 p (fun _ => 0)) = _ at hc
  rw [Paper7Setup.sg_order,← he.1 1,hm1] at hc
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero] at hc
  omega
#print axioms Paper7B4Analytic.three_positive_big_card

theorem qzero_big_nodup (p : Fin 4 → ℕ) (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    (Bplus (SG 4 p (fun _ => 0))).Nodup := by
  apply Multiset.nodup_iff_count_le_one.mpr
  intro x
  by_cases hx : 2 ≤ x
  · exact qzero_big_count_le_one p hn hG x hx
  · simp [Bplus,hx]
#print axioms Paper7B4Analytic.qzero_big_nodup

theorem three_positive_integer_roots (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hn : nOf 4 p (fun _ => 0) ≤ 49) (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    ∃ r s t : ℕ, 2 ≤ r ∧ r < s ∧ s < t ∧ r^2+s^2+t^2 ≤ 49 ∧
      (r : ℝ) ∈ spec (SG 4 p (fun _ => 0)) ∧
      (s : ℝ) ∈ spec (SG 4 p (fun _ => 0)) ∧
      (t : ℝ) ∈ spec (SG 4 p (fun _ => 0)) := by
  have hcard := three_positive_big_card p hp0 hp1 hp2 hp3 hG
  obtain ⟨x,y,z,hs⟩ := Multiset.card_eq_three.mp hcard
  have hx : x ∈ Bplus (SG 4 p (fun _ => 0)) := by rw [hs]; simp
  have hy : y ∈ Bplus (SG 4 p (fun _ => 0)) := by rw [hs]; simp
  have hz : z ∈ Bplus (SG 4 p (fun _ => 0)) := by rw [hs]; simp
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
  have hnodup := qzero_big_nodup p hn hG
  rw [hs] at hnodup
  have hdistinct : x ≠ y ∧ x ≠ z ∧ y ≠ z := by simpa [and_assoc] using hnodup
  have hXY : X.toNat ≠ Y.toNat := by
    intro hh; apply hdistinct.1; rw [← hXn,← hYn,hh]
  have hXZ : X.toNat ≠ Z.toNat := by
    intro hh; apply hdistinct.2.1; rw [← hXn,← hZn,hh]
  have hYZ : Y.toNat ≠ Z.toNat := by
    intro hh; apply hdistinct.2.2; rw [← hYn,← hZn,hh]
  have hsumR : x^2+y^2+z^2 ≤ 49 := by
    have hS := (Paper7Counting.lemma42_bounds 4 p (fun _ => 0) (by decide)
      (by decide) hG).1
    have hnr : (nOf 4 p (fun _ => 0) : ℝ) ≤ 49 := by exact_mod_cast hn
    have he : S2 (SG 4 p (fun _ => 0)) = x^2+y^2+z^2 := by simp [S2,hs]; ring
    rw [he] at hS
    linarith
  have hsum : X.toNat^2+Y.toNat^2+Z.toNat^2 ≤ 49 := by
    have hh : (X.toNat : ℝ)^2+(Y.toNat : ℝ)^2+(Z.toNat : ℝ)^2 ≤ 49 := by
      rw [hXn,hYn,hZn]; exact hsumR
    exact_mod_cast hh
  have hXm : (X.toNat : ℝ) ∈ spec (SG 4 p (fun _ => 0)) := by rw [hXn]; exact hxm
  have hYm : (Y.toNat : ℝ) ∈ spec (SG 4 p (fun _ => 0)) := by rw [hYn]; exact hym
  have hZm : (Z.toNat : ℝ) ∈ spec (SG 4 p (fun _ => 0)) := by rw [hZn]; exact hzm
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
#print axioms Paper7B4Analytic.three_positive_integer_roots

theorem ordered_three_square_profiles (r s t : ℕ) (hr : 2 ≤ r)
    (hrs : r < s) (hst : s < t) (hsum : r^2+s^2+t^2 ≤ 49) :
    (r = 2 ∧ s = 3 ∧ (t = 4 ∨ t = 5 ∨ t = 6)) ∨
      (r = 2 ∧ s = 4 ∧ t = 5) := by
  have hr2 : r = 2 := by
    by_contra hh
    have hr3 : 3 ≤ r := by omega
    have hs4 : 4 ≤ s := by omega
    have ht5 : 5 ≤ t := by omega
    nlinarith
  have hs3 : 3 ≤ s := by omega
  have hs4 : s ≤ 4 := by
    by_contra hh
    have hs5 : 5 ≤ s := by omega
    have ht6 : 6 ≤ t := by omega
    nlinarith
  have hscases : s = 3 ∨ s = 4 := by omega
  rcases hscases with hs | hs
  · left
    refine ⟨hr2,hs,?_⟩
    have ht6 : t ≤ 6 := by
      by_contra hh
      have ht7 : 7 ≤ t := by omega
      nlinarith
    omega
  · right
    refine ⟨hr2,hs,?_⟩
    have ht5 : t ≤ 5 := by
      by_contra hh
      have ht6 : 6 ≤ t := by omega
      nlinarith
    omega
#print axioms Paper7B4Analytic.ordered_three_square_profiles

end Paper7B4Analytic
