import Research.Backfill.Paper7.B4OppositePOverlap
import Research.Backfill.Paper7.B4PerronBounds

/-! Source-only quartic and monodromy rigidity for disjoint opposite P/Q. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def disjointOppositeQuartic (a c b d t : ℝ) : ℝ :=
  (t-a)*(t-c)*(t-b-1)*(t-d-1)-(t-1)*(2*t-a-c)*(2*t-b-d-2)
#print axioms Paper7B4Analytic.disjointOppositeQuartic

theorem disjoint_opposite_factor (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0) (t : ℝ) :
    mixedPolynomial p q t = t^2*(t-1)^2*disjointOppositeQuartic (p 0) (p 2) (q 1) (q 3) t := by
  unfold mixedPolynomial mixedLocalPolynomial disjointOppositeQuartic
  rw [hp1,hp3,hq0,hq2]
  norm_num
  ring
#print axioms Paper7B4Analytic.disjoint_opposite_factor

theorem disjoint_opposite_ordinary_spec_iff (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0)
    (m : ℝ) (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p q) ↔ disjointOppositeQuartic (p 0) (p 2) (q 1) (q 3) (m^2) = 0 := by
  rw [mixed_ordinary_spec_iff p q m hmn hm0 hm1,disjoint_opposite_factor p q hp1 hp3 hq0 hq2]
  have hd : m^2-1 ≠ 0 := by
    intro hh
    have hp : (m-1)*(m+1) = 0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp hp with h | h
    · exact hm1 (by linarith)
    · exact hmn (by linarith)
  exact mul_eq_zero_iff_left (mul_ne_zero (pow_ne_zero 2 (pow_ne_zero 2 hm0)) (pow_ne_zero 2 hd))
#print axioms Paper7B4Analytic.disjoint_opposite_ordinary_spec_iff

theorem disjoint_opposite_identity_data (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0)
    (m : ℕ) (hm : 2 ≤ m) (hid : Mono 4 p q m = 1) :
    p 0+p 2 = 2*m^2 ∧ q 1+q 3 = 2*(m^2-1) ∧
      ((p 0 = m^2 ∧ p 2 = m^2) ∨ (q 1 = m^2-1 ∧ q 3 = m^2-1)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hd : (m : ℝ)^2-1 ≠ 0 := by nlinarith
  have hmN : 1 ≤ m^2 := by nlinarith
  have hcast : ((m^2-1 : ℕ) : ℝ) = (m : ℝ)^2-1 := by
    simp only [Nat.cast_sub hmN,Nat.cast_pow,Nat.cast_one]
  have hprod : realFourProduct ((m : ℝ)-(p 0 : ℝ)/m)
      ((m : ℝ)-(q 1 : ℝ)*m/((m : ℝ)^2-1)) ((m : ℝ)-(p 2 : ℝ)/m)
      ((m : ℝ)-(q 3 : ℝ)*m/((m : ℝ)^2-1)) = 1 := by
    simpa [mono_four_product,fk,hp1,hp3,hq0,hq2] using hid
  obtain ⟨h02,h13,h01⟩ := real_four_identity_data _ _ _ _ hprod
  have he02 : (m : ℝ)*(((m : ℝ)-(p 0 : ℝ)/m)+((m : ℝ)-(p 2 : ℝ)/m)) =
      2*(m : ℝ)^2-p 0-p 2 := by field_simp [hm0]; ring
  have he13 : (((m : ℝ)^2-1)/m)*(((m : ℝ)-(q 1 : ℝ)*m/((m : ℝ)^2-1))+
      ((m : ℝ)-(q 3 : ℝ)*m/((m : ℝ)^2-1))) = 2*((m : ℝ)^2-1)-q 1-q 3 := by
    field_simp [hm0,hd]
    ring
  rw [h02,mul_zero] at he02
  rw [h13,mul_zero] at he13
  have hpR : (p 0 : ℝ)+p 2 = 2*(m : ℝ)^2 := by linarith
  have hqR : (q 1 : ℝ)+q 3 = 2*((m : ℝ)^2-1) := by linarith
  have hp : p 0+p 2 = 2*m^2 := by exact_mod_cast hpR
  have hq : q 1+q 3 = 2*(m^2-1) := by rw [← hcast] at hqR; exact_mod_cast hqR
  refine ⟨hp,hq,?_⟩
  rcases mul_eq_zero.mp h01 with h0 | h1
  · have he : ((m : ℝ)-(p 0 : ℝ)/m)*m = (m : ℝ)^2-p 0 := by
      field_simp [hm0]
    rw [h0,zero_mul] at he
    have hp0R : (p 0 : ℝ) = (m : ℝ)^2 := by nlinarith only [he]
    have hp0 : p 0 = m^2 := by exact_mod_cast hp0R
    exact Or.inl ⟨hp0,by omega⟩
  · have he : ((m : ℝ)-(q 1 : ℝ)*m/((m : ℝ)^2-1))*((m : ℝ)^2-1)/m =
        (m : ℝ)^2-1-q 1 := by
      field_simp [hm0,hd]
    rw [h1,zero_mul,zero_div] at he
    have hq1R : (q 1 : ℝ) = (m : ℝ)^2-1 := by nlinarith only [he]
    have hq1 : q 1 = m^2-1 := by rw [← hcast] at hq1R; exact_mod_cast hq1R
    exact Or.inr ⟨hq1,by omega⟩
#print axioms Paper7B4Analytic.disjoint_opposite_identity_data

theorem disjoint_opposite_identity_order (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0)
    (m : ℕ) (hm : 2 ≤ m) (hid : Mono 4 p q m = 1) : nOf 4 p q = 6*m^2 := by
  obtain ⟨hp,hq,_hc⟩ := disjoint_opposite_identity_data p q hp1 hp3 hq0 hq2 m hm hid
  have hmN : 1 ≤ m^2 := by nlinarith
  simp only [nOf,Fin.sum_univ_four,hp1,hp3,hq0,hq2,Nat.add_zero,Nat.zero_add]
  omega
#print axioms Paper7B4Analytic.disjoint_opposite_identity_order

theorem disjoint_opposite_factor_p_four (b d t : ℝ) (hs : b+d = 6) :
    disjointOppositeQuartic 4 4 b d t = (t-4)^2*(t^2-12*t+b*d+11) := by
  have hd : d = 6-b := by linarith
  rw [hd]
  unfold disjointOppositeQuartic
  ring
#print axioms Paper7B4Analytic.disjoint_opposite_factor_p_four

theorem disjoint_opposite_factor_q_three (a c t : ℝ) (hs : a+c = 8) :
    disjointOppositeQuartic a c 3 3 t = (t-4)^2*(t^2-12*t+a*c+4) := by
  have hc : c = 8-a := by linarith
  rw [hc]
  unfold disjointOppositeQuartic
  ring
#print axioms Paper7B4Analytic.disjoint_opposite_factor_q_three

theorem perron_square_twelve_impossible (R : ℕ) (C : ℝ) (hR : 3 ≤ R)
    (hC0 : 0 < C) (hC20 : C ≤ 20) (he : (R : ℝ)^4-12*(R : ℝ)^2+C = 0) : False := by
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hsq : (R : ℝ)^2 ≤ 12 := by
    by_contra hh
    have hprod : 0 < (R : ℝ)^2*((R : ℝ)^2-12) := mul_pos (by nlinarith) (by linarith)
    nlinarith only [he,hC0,hprod]
  have hsqN : R^2 ≤ 12 := by exact_mod_cast hsq
  have hR3 : R = 3 := by
    by_contra hh
    have hR4 : 4 ≤ R := by omega
    have hh := Nat.pow_le_pow_left hR4 2
    norm_num at hh
    omega
  rw [hR3] at he
  norm_num at he
  linarith
#print axioms Paper7B4Analytic.perron_square_twelve_impossible

theorem disjoint_opposite_no_repeated_nat (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0)
    (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q)) (m : ℕ) (hm : 2 ≤ m) :
    mult (SG 4 p q) m ≠ 2 := by
  intro hmult
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hid := (Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p q (by decide) m
    (by linarith) (by linarith) (by linarith)).2.2.1.mp hmult
  have hord := disjoint_opposite_identity_order p q hp1 hp3 hq0 hq2 m hm hid
  have hm2 : m = 2 := by
    by_contra hh
    have hm3 : 3 ≤ m := by omega
    have hh := Nat.pow_le_pow_left hm3 2
    norm_num at hh
    omega
  subst m
  obtain ⟨hpsum,hqsum,hcases⟩ := disjoint_opposite_identity_data p q hp1 hp3 hq0 hq2 2 (by decide) hid
  norm_num at hpsum hqsum hcases
  have hpend : 0 < ∑ i, (p i+q i) := by rw [Fin.sum_univ_four]; omega
  obtain ⟨R,hR,hmem,_hmax⟩ := integral_perron_integer p q hpend hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have he := (disjoint_opposite_ordinary_spec_iff p q hp1 hp3 hq0 hq2 R
    (by linarith) (by linarith) (by linarith)).mp hmem
  have hdiff : (R : ℝ)^2-4 ≠ 0 := by nlinarith
  have hpR : (p 0 : ℝ)+p 2 = 8 := by exact_mod_cast hpsum
  have hqR : (q 1 : ℝ)+q 3 = 6 := by exact_mod_cast hqsum
  rcases hcases with ⟨ha,hc⟩ | ⟨hb,hd⟩
  · rw [ha,hc] at he
    norm_num only [Nat.cast_ofNat] at he
    rw [disjoint_opposite_factor_p_four _ _ _ hqR] at he
    have hh := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hdiff)
    have hqSq := congrArg (fun x : ℝ => x^2) hqR
    have hC20 : (q 1 : ℝ)*q 3+11 ≤ 20 := by nlinarith only [hqSq,sq_nonneg ((q 1 : ℝ)-q 3)]
    exact perron_square_twelve_impossible R ((q 1 : ℝ)*q 3+11) hR (by positivity) hC20 (by nlinarith only [hh])
  · rw [hb,hd] at he
    norm_num only [Nat.cast_ofNat] at he
    rw [disjoint_opposite_factor_q_three _ _ _ hpR] at he
    have hh := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hdiff)
    have hpSq := congrArg (fun x : ℝ => x^2) hpR
    have hC20 : (p 0 : ℝ)*p 2+4 ≤ 20 := by nlinarith only [hpSq,sq_nonneg ((p 0 : ℝ)-p 2)]
    exact perron_square_twelve_impossible R ((p 0 : ℝ)*p 2+4) hR (by positivity) hC20 (by nlinarith only [hh])
#print axioms Paper7B4Analytic.disjoint_opposite_no_repeated_nat

theorem disjoint_opposite_multiplicity_le_one (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hq0 : q 0 = 0) (hq2 : q 2 = 0)
    (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q)) (x : ℝ) (hx : 2 ≤ x) :
    mult (SG 4 p q) x ≤ 1 := by
  have hcl := Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p q (by decide) x
    (by linarith) (by linarith) (by linarith)
  by_contra hh
  have hmult : mult (SG 4 p q) x = 2 := by have hb := hcl.2.1; omega
  have hmem : x ∈ spec (SG 4 p q) := Multiset.count_pos.mp (by change 0 < mult (SG 4 p q) x; omega)
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG x hmem
  have hz2 : (2 : ℤ) ≤ z := by rw [hz] at hx; exact_mod_cast hx
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hzr : (z.toNat : ℝ) = x := by
    have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
    exact hc.trans hz.symm
  apply disjoint_opposite_no_repeated_nat p q hp0 hp1 hp3 hq0 hq2 hn hG z.toNat (by omega)
  simpa only [hzr] using hmult
#print axioms Paper7B4Analytic.disjoint_opposite_multiplicity_le_one

end Paper7B4Analytic
