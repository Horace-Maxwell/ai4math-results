import Research.Backfill.Paper7.B4QzeroSimpleSpectrum
import Research.Backfill.Paper7.Lemma42

/-! Source-only access to the exceptional root 1 for arbitrary q=0 parameters.
The transfer kernel is identified with the exceptional kernel, so no ordinary
root exclusion is silently applied at 1. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem qzero_unit_multiplicity_monodromy (p : Fin 4 → ℕ) :
    mult (SG 4 p (fun _ => 0)) 1 = matrixNullity (Mono 4 p (fun _ => 0) 1-1) := by
  have hK : Kq 4 (fun _ => 0) = ∅ := by simp [Kq]
  have hoff := ((Paper7Lemma22.check_Lemma22 4 p (fun _ => 0)
    (by decide)).2.2.1 1 (Or.inl rfl)).1
  have hmult : mult (SG 4 p (fun _ => 0)) 1 = deltaE 4 p (fun _ => 0) 1 := by
    simpa [hK] using hoff
  have hker : LinearMap.ker (Matrix.toLin' (Wmat 4 p (fun _ => 0) 1)) =
      LinearMap.ker (Matrix.toLin' (Smat 4 p (fun _ => 0) 1)) := by
    apply Submodule.ext
    intro y
    rw [Paper7Lemma22Gaps.mem_ker_Wmat_iff_of_empty 4 p (fun _ => 0) 1 hK y,
      Paper7Lemma22Periodic.mem_ker_smat_iff 4 p (fun _ => 0) 1 (by decide) y]
    simp [fk]
  calc
    _ = deltaE 4 p (fun _ => 0) 1 := hmult
    _ = matrixNullity (Smat 4 p (fun _ => 0) 1) := by
      change Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Wmat 4 p (fun _ => 0) 1))) = _
      rw [hker]
      rfl
    _ = _ := (Paper7Lemma22Periodic.smatKernelEquivMono 4 p (fun _ => 0) 1
      (by decide)).finrank_eq
#print axioms Paper7B4Analytic.qzero_unit_multiplicity_monodromy

theorem qzero_unit_trace_iff_spec (p : Fin 4 → ℕ) :
    (Mono 4 p (fun _ => 0) 1).trace = 2 ↔ 1 ∈ spec (SG 4 p (fun _ => 0)) := by
  have hm := qzero_unit_multiplicity_monodromy p
  have hc := Paper7Lemma22.monodromy_kernel_classification 4 p (fun _ => 0) 1
  rw [← hm] at hc
  constructor
  · intro ht
    have hpos : 0 < mult (SG 4 p (fun _ => 0)) 1 := by
      by_cases hid : Mono 4 p (fun _ => 0) 1 = 1
      · have hh := hc.2.1.mpr hid
        omega
      · have hh := hc.2.2.mpr ⟨hid,ht⟩
        omega
    exact Multiset.count_pos.mp hpos
  · intro hmem
    have hpos : 0 < mult (SG 4 p (fun _ => 0)) 1 := Multiset.count_pos.mpr hmem
    have hcases : mult (SG 4 p (fun _ => 0)) 1 = 1 ∨
        mult (SG 4 p (fun _ => 0)) 1 = 2 := by omega
    rcases hcases with h1 | h2
    · exact (hc.2.2.mp h1).2
    · rw [hc.2.1.mp h2]
      norm_num [Matrix.trace,Fin.sum_univ_two]
#print axioms Paper7B4Analytic.qzero_unit_trace_iff_spec

theorem qzero_unit_spec_iff (p : Fin 4 → ℕ) :
    1 ∈ spec (SG 4 p (fun _ => 0)) ↔
      qzeroQuartic (p 0) (p 1) (p 2) (p 3) 1 = 0 := by
  have he : (Mono 4 p (fun _ => 0) 1).trace-2 =
      qzeroQuartic (p 0) (p 1) (p 2) (p 3) 1 := by
    rw [mono_four_product]
    simpa [fk] using qzero_four_trace_identity (p 0) (p 1) (p 2) (p 3) 1 (by norm_num)
  rw [← qzero_unit_trace_iff_spec p]
  constructor <;> intro h <;> linarith
#print axioms Paper7B4Analytic.qzero_unit_spec_iff

theorem even_integral_large_square_le_order (p q : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 p q)) (x : ℝ) (hx : x ∈ spec (SG 4 p q))
    (hx2 : 2 ≤ x) : x^2 ≤ (nOf 4 p q : ℝ) := by
  have hmem : x ∈ Bplus (SG 4 p q) := Multiset.mem_filter.mpr ⟨hx,hx2⟩
  have hnonneg : ∀ z ∈ (Bplus (SG 4 p q)).map (fun y => y^2), (0 : ℝ) ≤ z := by
    intro z hz
    obtain ⟨y,_hy,rfl⟩ := Multiset.mem_map.mp hz
    exact sq_nonneg y
  have hle : x^2 ≤ S2 (SG 4 p q) :=
    Multiset.single_le_sum hnonneg (x^2) (Multiset.mem_map.mpr ⟨x,hmem,rfl⟩)
  exact hle.trans (Paper7Counting.lemma42_bounds 4 p q (by decide) (by decide) hG).1
#print axioms Paper7B4Analytic.even_integral_large_square_le_order

theorem qzero_small_order_nonintegral (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, p k) (hn : nOf 4 p (fun _ => 0) ≤ 8) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  have hpend : 0 < ∑ k, (p k+(0 : ℕ)) := by simpa using hp
  obtain ⟨R,hR,hmem,_hmax⟩ := integral_perron_integer p (fun _ => 0) hpend hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hs := even_integral_large_square_le_order p (fun _ => 0) hG R hmem (by linarith)
  have hnr : (nOf 4 p (fun _ => 0) : ℝ) ≤ 8 := by exact_mod_cast hn
  nlinarith
#print axioms Paper7B4Analytic.qzero_small_order_nonintegral

theorem qzero_unit_multiplicity_le_one (p : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    mult (SG 4 p (fun _ => 0)) 1 ≤ 1 := by
  have hm := qzero_unit_multiplicity_monodromy p
  have hc := Paper7Lemma22.monodromy_kernel_classification 4 p (fun _ => 0) 1
  rw [← hm] at hc
  by_contra hh
  have htwo : mult (SG 4 p (fun _ => 0)) 1 = 2 := by omega
  have hid := hc.2.1.mp htwo
  obtain ⟨h02,h13,_hcases⟩ := qzero_identity_parameter_data p 1 (by decide) (by simpa only [Nat.cast_one] using hid)
  norm_num at h02 h13
  have hsum : ∑ k, p k = 4 := by rw [Fin.sum_univ_four]; omega
  have hn : nOf 4 p (fun _ => 0) ≤ 8 := by simp [nOf,hsum]
  exact qzero_small_order_nonintegral p (by omega) hn hG
#print axioms Paper7B4Analytic.qzero_unit_multiplicity_le_one

end Paper7B4Analytic
