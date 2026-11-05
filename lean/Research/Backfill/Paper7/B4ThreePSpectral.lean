import Research.Backfill.Paper7.B4PerronBounds

/-! Source-only real spectral reduction for q=0 with one zero site, and the
complete integer-root data for equal opposite positive P1 loads. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Matrix Classical

def threePCubic (a b c t : ℝ) : ℝ :=
  (t-a)*(t-b)*(t-c)-(2*t-a-c)*(2*t-b)
#print axioms Paper7B4Analytic.threePCubic

theorem three_p_trace_identity (a b c m : ℝ) (hm : m ≠ 0) :
    m^2*((realFourProduct (m-a/m) (m-b/m) (m-c/m) m).trace-2) =
      threePCubic a b c (m^2) := by
  rw [real_four_trace]
  unfold threePCubic
  field_simp [hm]; ring
#print axioms Paper7B4Analytic.three_p_trace_identity

theorem three_p_ordinary_spec_iff (p : Fin 4 → ℕ) (hp3 : p 3 = 0) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p (fun _ => 0)) ↔ threePCubic (p 0) (p 1) (p 2) (m^2) = 0 := by
  have he : m^2*((Mono 4 p (fun _ => 0) m).trace-2) =
      threePCubic (p 0) (p 1) (p 2) (m^2) := by
    rw [mono_four_product]
    simpa [fk,hp3] using three_p_trace_identity (p 0) (p 1) (p 2) m hm0
  rw [← ordinary_trace_iff_spec p (fun _ => 0) m hmn hm0 hm1]
  constructor
  · intro h
    rw [h] at he
    nlinarith only [he]
  · intro h
    rw [h] at he
    have hz := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hm0)
    linarith only [hz]
#print axioms Paper7B4Analytic.three_p_ordinary_spec_iff

theorem symmetric_three_p_factor (a b t : ℝ) :
    threePCubic a b a t = (t-a)*(t^2-(a+b+4)*t+b*(a+2)) := by
  unfold threePCubic
  ring
#print axioms Paper7B4Analytic.symmetric_three_p_factor

theorem symmetric_three_p_endpoint_square (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp2 : p 2 = p 0) (hp3 : p 3 = 0)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    ∃ l : ℕ, 1 ≤ l ∧ p 0 = l^2 := by
  by_cases hunit : p 0 = 1
  · exact ⟨1,by omega,by simpa using hunit⟩
  let s : ℝ := Real.sqrt (p 0)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
  have hsq : s^2 = (p 0 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : s ≠ 1 := by
    intro h
    have hh : (p 0 : ℝ) = 1 := by rw [h] at hsq; nlinarith only [hsq]
    exact hunit (by exact_mod_cast hh)
  have he : threePCubic (p 0) (p 1) (p 2) (s^2) = 0 := by
    rw [hp2,symmetric_three_p_factor,hsq]
    ring
  have hmem := (three_p_ordinary_spec_iff p hp3 s (by linarith) (by linarith) hs1).mpr he
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p (fun _ => 0)) hG s hmem
  have hzpos : (0 : ℤ) < z := by rw [hz] at hs0; exact_mod_cast hs0
  have hn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hnR : (z.toNat : ℝ) = s := by
    have hh : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hn
    exact hh.trans hz.symm
  refine ⟨z.toNat,by omega,?_⟩
  have hh : (p 0 : ℝ) = (z.toNat : ℝ)^2 := by rw [hnR]; exact hsq.symm
  exact_mod_cast hh
#print axioms Paper7B4Analytic.symmetric_three_p_endpoint_square

theorem symmetric_three_p_integer_roots (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : p 2 = p 0) (hp3 : p 3 = 0)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    ∃ l R S : ℕ, 1 ≤ l ∧ 3 ≤ R ∧ 1 ≤ S ∧ p 0 = l^2 ∧
      p 0+p 1+4 = R^2+S^2 ∧ p 1*(p 0+2) = R^2*S^2 ∧ p 0+3 ≤ R^2 := by
  obtain ⟨l,hl,hpl⟩ := symmetric_three_p_endpoint_square p hp0 hp2 hp3 hG
  have hp : 0 < ∑ k, (p k+(0 : ℕ)) := by
    have hle : p 0 ≤ ∑ k, p k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    simpa only [Nat.add_zero] using hp0.trans_le hle
  obtain ⟨R,hR,hmem,_hbound,hcap⟩ := integral_perron_load_data p (fun _ => 0) hp hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hc0 : (p 0 : ℝ)+3 ≤ (R : ℝ)^2 := by
    have hh := hcap 0
    simp only [Nat.add_zero] at hh
    exact_mod_cast hh
  have he := (three_p_ordinary_spec_iff p hp3 R (by linarith) (by linarith)
    (by linarith)).mp hmem
  rw [hp2,symmetric_three_p_factor] at he
  have hfac : (R : ℝ)^2-(p 0 : ℝ) ≠ 0 := by linarith
  have hpoly := (mul_eq_zero.mp he).resolve_left hfac
  let t : ℝ := (p 0 : ℝ)+p 1+4-(R : ℝ)^2
  have hsum : (p 0 : ℝ)+p 1+4 = (R : ℝ)^2+t := by dsimp [t]; ring
  have hprod : (R : ℝ)^2*t = (p 1 : ℝ)*((p 0 : ℝ)+2) := by
    dsimp [t]
    nlinarith only [hpoly]
  have hrhs : 0 < (p 1 : ℝ)*((p 0 : ℝ)+2) :=
    mul_pos (by exact_mod_cast hp1) (by positivity)
  have ht : 0 < t := by
    by_contra h
    have hh := mul_nonneg (sq_nonneg (R : ℝ)) (show 0 ≤ -t by linarith)
    nlinarith only [hprod,hrhs,hh]
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht
  have hsq : s^2 = t := Real.sq_sqrt ht.le
  have hsInteger : ∃ S : ℕ, 1 ≤ S ∧ (S : ℝ) = s := by
    by_cases hs1 : s = 1
    · exact ⟨1,by omega,by simpa using hs1.symm⟩
    have hspoly : s^4-((p 0 : ℝ)+p 1+4)*s^2+(p 1 : ℝ)*((p 0 : ℝ)+2) = 0 := by
      calc
        _ = (s^2-(R : ℝ)^2)*(s^2-t) := by rw [hsum,← hprod]; ring
        _ = 0 := by rw [hsq]; ring
    have hsroot : threePCubic (p 0) (p 1) (p 2) (s^2) = 0 := by
      rw [hp2,symmetric_three_p_factor]
      have hpow : (s^2)^2 = s^4 := by ring
      rw [hpow,hspoly,mul_zero]
    have hsmem := (three_p_ordinary_spec_iff p hp3 s
      (by linarith) (by linarith) hs1).mpr hsroot
    obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p (fun _ => 0)) hG s hsmem
    have hzpos : (0 : ℤ) < z := by rw [hz] at hs0; exact_mod_cast hs0
    have hn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have hnR : (z.toNat : ℝ) = s := by
      have hh : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hn
      exact hh.trans hz.symm
    exact ⟨z.toNat,by omega,hnR⟩
  obtain ⟨S,hS,hSr⟩ := hsInteger
  refine ⟨l,R,S,hl,hR,hS,hpl,?_,?_,?_⟩
  · have hh : (p 0 : ℝ)+p 1+4 = (R : ℝ)^2+(S : ℝ)^2 := by
      rw [hSr,hsq]
      exact hsum
    exact_mod_cast hh
  · have hh : (p 1 : ℝ)*((p 0 : ℝ)+2) = (R : ℝ)^2*(S : ℝ)^2 := by
      rw [hSr,hsq]
      exact hprod.symm
    exact_mod_cast hh
  · simpa only [Nat.add_zero] using hcap 0
#print axioms Paper7B4Analytic.symmetric_three_p_integer_roots

end Paper7B4Analytic
