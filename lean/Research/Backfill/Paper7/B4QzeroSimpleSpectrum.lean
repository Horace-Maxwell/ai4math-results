import Research.Backfill.Paper7.B4QzeroQuartic

/-! Source-only exclusion of all repeated positive ordinary eigenvalues for
integral q=0 graphs of order at most 49. All p coordinates are arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem qzero_identity_perron_data (p : Fin 4 → ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hid : Mono 4 p (fun _ => 0) m = 1)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    ∃ R b d : ℕ, m < R ∧ b+d = 2*m^2 ∧
      (R : ℝ)^4-(2*(m : ℝ)^2+4)*(R : ℝ)^2+(b : ℝ)*d = 0 := by
  obtain ⟨hs02,hs13,hcases⟩ := qzero_identity_parameter_data p m (by omega) hid
  have hm2pos : 0 < m^2 := pow_pos (by omega) 2
  have hp : 0 < ∑ k, (p k+(0 : ℕ)) := by
    norm_num [Fin.sum_univ_four]
    omega
  obtain ⟨R,hR,hmem,_hbound,hcap⟩ := integral_perron_load_data p (fun _ => 0) hp hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have he := (qzero_ordinary_spec_iff p R (by linarith) (by linarith)
    (by linarith)).mp hmem
  have hs02R : (p 0 : ℝ)+p 2 = 2*(m : ℝ)^2 := by exact_mod_cast hs02
  have hs13R : (p 1 : ℝ)+p 3 = 2*(m : ℝ)^2 := by exact_mod_cast hs13
  rcases hcases with ⟨h0,h2⟩ | ⟨h1,h3⟩
  · have hload : m^2+3 ≤ R^2 := by simpa [h0] using hcap 0
    have hloadR : (m : ℝ)^2+3 ≤ (R : ℝ)^2 := by exact_mod_cast hload
    have hRm : m < R := by
      by_contra hh
      have hh' : R ≤ m := by omega
      have hs := Nat.pow_le_pow_left hh' 2
      omega
    have hdiff : (R : ℝ)^2-(m : ℝ)^2 ≠ 0 := by linarith
    rw [h0,h2] at he
    push_cast at he
    rw [qzero_quartic_factor_even _ _ _ _ hs13R] at he
    have hquad := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hdiff)
    refine ⟨R,p 1,p 3,hRm,hs13,?_⟩
    nlinarith only [hquad]
  · have hload : m^2+3 ≤ R^2 := by simpa [h1] using hcap 1
    have hloadR : (m : ℝ)^2+3 ≤ (R : ℝ)^2 := by exact_mod_cast hload
    have hRm : m < R := by
      by_contra hh
      have hh' : R ≤ m := by omega
      have hs := Nat.pow_le_pow_left hh' 2
      omega
    have hdiff : (R : ℝ)^2-(m : ℝ)^2 ≠ 0 := by linarith
    rw [h1,h3] at he
    push_cast at he
    rw [qzero_quartic_factor_odd _ _ _ _ hs02R] at he
    have hquad := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hdiff)
    refine ⟨R,p 0,p 2,hRm,hs02,?_⟩
    nlinarith only [hquad]
#print axioms Paper7B4Analytic.qzero_identity_perron_data

theorem small_repeat_perron_impossible (m R b d : ℕ) (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hRm : m < R) (hs : b+d = 2*m^2)
    (he : (R : ℝ)^4-(2*(m : ℝ)^2+4)*(R : ℝ)^2+(b : ℝ)*d = 0) : False := by
  have hsR : (b : ℝ)+d = 2*(m : ℝ)^2 := by exact_mod_cast hs
  have hsquare := congrArg (fun x : ℝ => x^2) hsR
  have hbd : 0 ≤ (b : ℝ)*d := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hRposN : 0 < R := by omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hRposN
  have ht : (0 : ℝ) < (R : ℝ)^2 := sq_pos_of_pos hRpos
  have hbound : (R : ℝ)^2 ≤ 2*(m : ℝ)^2+4 := by
    by_contra hh
    have hfactor : 0 < (R : ℝ)^2*((R : ℝ)^2-(2*(m : ℝ)^2+4)) :=
      mul_pos ht (by linarith)
    nlinarith only [he,hbd,hfactor]
  have hboundN : R^2 ≤ 2*m^2+4 := by exact_mod_cast hbound
  have hcases : m = 2 ∨ m = 3 := by omega
  rcases hcases with hm | hm
  · subst m
    have hRupper : R ≤ 3 := by
      by_contra hh
      have hfour : 4 ≤ R := by omega
      have hsq := Nat.pow_le_pow_left hfour 2
      norm_num at hboundN hsq
      omega
    have hReq : R = 3 := by omega
    subst R
    norm_num at hsquare he
    nlinarith only [hsquare,he,sq_nonneg ((b : ℝ)-(d : ℝ))]
  · subst m
    have hRupper : R ≤ 4 := by
      by_contra hh
      have hfive : 5 ≤ R := by omega
      have hsq := Nat.pow_le_pow_left hfive 2
      norm_num at hboundN hsq
      omega
    have hReq : R = 4 := by omega
    subst R
    norm_num at hsquare he
    nlinarith only [hsquare,he,sq_nonneg ((b : ℝ)-(d : ℝ))]
#print axioms Paper7B4Analytic.small_repeat_perron_impossible

theorem qzero_no_repeated_ordinary_nat (p : Fin 4 → ℕ)
    (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) (m : ℕ) (hm : 2 ≤ m) :
    mult (SG 4 p (fun _ => 0)) m ≠ 2 := by
  intro hmult
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm3 : m ≤ 3 := by
    by_contra hh
    have hm4 : 4 ≤ m := by omega
    have hm4R : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    exact repeated_ordinary_below_four p (fun _ => 0) hn m hm4R hmult
  have hid := (Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p (fun _ => 0)
    (by decide) m (by linarith) (by linarith) (by linarith)).2.2.1.mp hmult
  obtain ⟨R,b,d,hRm,hs,he⟩ := qzero_identity_perron_data p m hm hid hG
  exact small_repeat_perron_impossible m R b d hm hm3 hRm hs he
#print axioms Paper7B4Analytic.qzero_no_repeated_ordinary_nat

theorem qzero_ordinary_multiplicity_le_one (p : Fin 4 → ℕ)
    (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) (x : ℝ) (hx : 2 ≤ x) :
    mult (SG 4 p (fun _ => 0)) x ≤ 1 := by
  have hclause := Paper7Lemma22Periodic.lemma22_ordinary_clause 4 p (fun _ => 0)
    (by decide) x (by linarith) (by linarith) (by linarith)
  have htwo := hclause.2.1
  by_contra hh
  have hmult : mult (SG 4 p (fun _ => 0)) x = 2 := by omega
  have hmem : x ∈ spec (SG 4 p (fun _ => 0)) :=
    Multiset.count_pos.mp (by change 0 < mult (SG 4 p (fun _ => 0)) x; omega)
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p (fun _ => 0)) hG x hmem
  have hz2 : (2 : ℤ) ≤ z := by rw [hz] at hx; exact_mod_cast hx
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hzr : (z.toNat : ℝ) = x := by
    have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
    exact hc.trans hz.symm
  have hm : 2 ≤ z.toNat := by omega
  have hnorep := qzero_no_repeated_ordinary_nat p hn hG z.toNat hm
  apply hnorep
  simpa only [hzr] using hmult
#print axioms Paper7B4Analytic.qzero_ordinary_multiplicity_le_one

end Paper7B4Analytic
