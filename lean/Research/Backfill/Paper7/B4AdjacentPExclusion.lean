import Research.Backfill.Paper7.B4PerronBounds

/-! Source-only exclusion of two adjacent positive P1 sites. Every real root
is connected to the actual spectrum through the successful monodromy API. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped BigOperators Matrix Classical

def adjacentPCubic (a b t : ℝ) : ℝ :=
  t^3-(a+b+4)*t^2+(a*b+2*a+2*b)*t-a*b
#print axioms Paper7B4Analytic.adjacentPCubic

theorem adjacent_p_trace_identity (a b m : ℝ) (hm : m ≠ 0) :
    m^2*((realFourProduct (m-a/m) (m-b/m) m m).trace-2) =
      adjacentPCubic a b (m^2) := by
  rw [real_four_trace]
  unfold adjacentPCubic
  field_simp [hm]; ring
#print axioms Paper7B4Analytic.adjacent_p_trace_identity

theorem adjacent_p_ordinary_spec_iff (p : Fin 4 → ℕ)
    (hp2 : p 2 = 0) (hp3 : p 3 = 0) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p (fun _ => 0)) ↔
      adjacentPCubic (p 0) (p 1) (m^2) = 0 := by
  have he : m^2*((Mono 4 p (fun _ => 0) m).trace-2) =
      adjacentPCubic (p 0) (p 1) (m^2) := by
    rw [mono_four_product]
    simpa [fk,hp2,hp3] using adjacent_p_trace_identity (p 0) (p 1) m hm0
  rw [← ordinary_trace_iff_spec p (fun _ => 0) m hmn hm0 hm1]
  constructor
  · intro h
    rw [h] at he
    nlinarith only [he]
  · intro h
    rw [h] at he
    have hdiff : (Mono 4 p (fun _ => 0) m).trace-2 = 0 :=
      (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hm0)
    linarith
#print axioms Paper7B4Analytic.adjacent_p_ordinary_spec_iff

theorem integral_no_spec_between_zero_one (p q : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 p q)) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    s ∉ spec (SG 4 p q) := by
  intro hmem
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p q) hG s hmem
  rw [hz] at hs0 hs1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hs0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast hs1
  omega
#print axioms Paper7B4Analytic.integral_no_spec_between_zero_one

theorem adjacent_p_cubic_positive (a b t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a+b ≤ 3) (ht : 9 ≤ t) :
    0 < adjacentPCubic a b t := by
  have he : adjacentPCubic a b t =
      t^2*(t-(a+b)-4)+(a*b)*(t-1)+(2*(a+b))*t := by
    unfold adjacentPCubic
    ring
  have hfirst : 0 < t^2*(t-(a+b)-4) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hsecond : 0 ≤ (a*b)*(t-1) :=
    mul_nonneg (mul_nonneg ha hb) (by linarith)
  have hthird : 0 ≤ (2*(a+b))*t := mul_nonneg (by linarith) (by linarith)
  rw [he]
  linarith
#print axioms Paper7B4Analytic.adjacent_p_cubic_positive

theorem adjacent_large_p_nonintegral (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : p 2 = 0) (hp3 : p 3 = 0)
    (hlarge : 3 < p 0+p 1) : ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  let f : ℝ → ℝ := adjacentPCubic (p 0) (p 1)
  have hcont : Continuous f := by
    change Continuous (fun t : ℝ => t^3-((p 0 : ℝ)+p 1+4)*t^2+
      ((p 0 : ℝ)*p 1+2*p 0+2*p 1)*t-(p 0 : ℝ)*p 1)
    fun_prop
  have hf0 : f 0 = -((p 0 : ℝ)*p 1) := by dsimp [f,adjacentPCubic]; ring
  have hf1 : f 1 = (p 0 : ℝ)+p 1-3 := by dsimp [f,adjacentPCubic]; ring
  have hprod : 0 < (p 0 : ℝ)*p 1 :=
    mul_pos (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hsum : (3 : ℝ) < (p 0 : ℝ)+p 1 := by exact_mod_cast hlarge
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by
    rw [hf0,hf1]
    exact ⟨by linarith,by linarith⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht.1
  have hsq : s^2 = t := Real.sq_sqrt ht.1.le
  have hs1 : s < 1 := by nlinarith [ht.2]
  have he : adjacentPCubic (p 0) (p 1) (s^2) = 0 := by
    rw [hsq]
    exact hft
  have hmem := (adjacent_p_ordinary_spec_iff p hp2 hp3 s
    (by linarith) (by linarith) (by linarith)).mpr he
  exact integral_no_spec_between_zero_one p (fun _ => 0) hG s hs0 hs1 hmem
#print axioms Paper7B4Analytic.adjacent_large_p_nonintegral

theorem adjacent_positive_p_nonintegral (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : p 2 = 0) (hp3 : p 3 = 0) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  by_cases hlarge : 3 < p 0+p 1
  · exact adjacent_large_p_nonintegral p hp0 hp1 hp2 hp3 hlarge hG
  have hsum : (p 0 : ℝ)+p 1 ≤ 3 := by
    have hh : p 0+p 1 ≤ 3 := by omega
    exact_mod_cast hh
  have hp : 0 < ∑ k, (p k+(0 : ℕ)) := by
    have hle : p 0 ≤ ∑ k, p k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    simpa only [Nat.add_zero] using hp0.trans_le hle
  obtain ⟨R,hR,hmem,_hbound⟩ := integral_perron_integer p (fun _ => 0) hp hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have he := (adjacent_p_ordinary_spec_iff p hp2 hp3 R
    (by linarith) (by linarith) (by linarith)).mp hmem
  have hpos := adjacent_p_cubic_positive (p 0) (p 1) ((R : ℝ)^2)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsum (by nlinarith)
  rw [he] at hpos
  exact (lt_irrefl 0) hpos
#print axioms Paper7B4Analytic.adjacent_positive_p_nonintegral

end Paper7B4Analytic
