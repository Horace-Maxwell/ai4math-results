import Research.Backfill.Paper7.B4ThreePDisjointPolynomial

/-! Source-only exclusion of repeated ordinary roots in the original order
range. Small repeats contradict the actual integral Perron root. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_disjoint_small_identity_parameters (a b c d m : ℕ)
    (hb : 0 < b) (hd : 0 < d) (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hid : Mono 4 (threePDisjointP a b c) (threePDisjointQ d) m = 1) :
    a+c = 2*m^2 ∧ b = m^2 ∧ d+1 = m^2 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hden : (m : ℝ)^2-1 ≠ 0 := by nlinarith
  have hprod : realFourProduct ((m : ℝ)-(a : ℝ)/m) ((m : ℝ)-(b : ℝ)/m)
      ((m : ℝ)-(c : ℝ)/m) ((m : ℝ)-(d : ℝ)*m/((m : ℝ)^2-1)) = 1 := by
    simpa [mono_four_product,fk,threePDisjointP,threePDisjointQ] using hid
  obtain ⟨h02,h13,_h01⟩ := real_four_identity_data _ _ _ _ hprod
  have he02 : (m : ℝ)*(((m : ℝ)-(a : ℝ)/m)+((m : ℝ)-(c : ℝ)/m)) =
      2*(m : ℝ)^2-a-c := by field_simp [hm0]; ring
  have he13 : (m : ℝ)*((m : ℝ)^2-1)*
      (((m : ℝ)-(b : ℝ)/m)+((m : ℝ)-(d : ℝ)*m/((m : ℝ)^2-1))) =
      2*(m : ℝ)^2*((m : ℝ)^2-1)-(b : ℝ)*((m : ℝ)^2-1)-(d : ℝ)*(m : ℝ)^2 := by
    field_simp [hm0,hden]
    ring
  rw [h02,mul_zero] at he02
  rw [h13,mul_zero] at he13
  have hs02R : (a : ℝ)+c = 2*(m : ℝ)^2 := by linarith only [he02]
  have hs02 : a+c = 2*m^2 := by exact_mod_cast hs02R
  have hs13R : (b : ℝ)*((m : ℝ)^2-1)+(d : ℝ)*(m : ℝ)^2 =
      2*(m : ℝ)^2*((m : ℝ)^2-1) := by linarith only [he13]
  refine ⟨hs02,?_⟩
  have hcases : m = 2 ∨ m = 3 := by omega
  rcases hcases with hm | hm
  · subst m
    norm_num at hs13R ⊢
    have he : b*3+d*4 = 24 := by exact_mod_cast hs13R
    omega
  · subst m
    norm_num at hs13R ⊢
    have he : b*8+d*9 = 144 := by exact_mod_cast hs13R
    omega
#print axioms Paper7B4Analytic.three_disjoint_small_identity_parameters

theorem three_disjoint_repeat_factor (a c M t : ℝ) (hs : a+c = 2*M) :
    threePDisjointQuartic a M c (M-1) t =
      (t-M)^2*(t^2-(2*M+4)*t+a*c+2) := by
  have hc : c = 2*M-a := by linarith only [hs]
  rw [hc]
  unfold threePDisjointQuartic
  ring
#print axioms Paper7B4Analytic.three_disjoint_repeat_factor

theorem three_disjoint_identity_perron_data (a b c d m : ℕ)
    (hb : 0 < b) (hd : 0 < d) (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hid : Mono 4 (threePDisjointP a b c) (threePDisjointQ d) m = 1)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d))) :
    ∃ R : ℕ, m < R ∧ a+c = 2*m^2 ∧
      (R : ℝ)^4-(2*(m : ℝ)^2+4)*(R : ℝ)^2+(a : ℝ)*c+2 = 0 := by
  obtain ⟨hs,hbM,hdM⟩ := three_disjoint_small_identity_parameters a b c d m hb hd hm2 hm3 hid
  have hpend : 0 < ∑ i, (threePDisjointP a b c i+threePDisjointQ d i) := by
    norm_num [threePDisjointP,threePDisjointQ,Fin.sum_univ_four]
    omega
  obtain ⟨R,hR,hmem,_hmax,hcap⟩ :=
    integral_perron_load_data (threePDisjointP a b c) (threePDisjointQ d) hpend hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hload : m^2+3 ≤ R^2 := by
    simpa [threePDisjointP,threePDisjointQ,hbM] using hcap 1
  have hloadR : (m : ℝ)^2+3 ≤ (R : ℝ)^2 := by exact_mod_cast hload
  have hRm : m < R := by
    by_contra hh
    have hle : R ≤ m := by omega
    have hsquare := Nat.pow_le_pow_left hle 2
    omega
  have hsR : (a : ℝ)+c = 2*(m : ℝ)^2 := by exact_mod_cast hs
  have hdR : (d : ℝ) = (m : ℝ)^2-1 := by
    have hh : (d : ℝ)+1 = (m : ℝ)^2 := by exact_mod_cast hdM
    linarith only [hh]
  have hH := (three_disjoint_ordinary_spec_iff a b c d R
    (by linarith) (by linarith) (by linarith)).mp hmem
  rw [hbM] at hH
  push_cast at hH
  rw [hdR,three_disjoint_repeat_factor _ _ _ _ hsR] at hH
  have hdiff : (R : ℝ)^2-(m : ℝ)^2 ≠ 0 := by linarith only [hloadR]
  have hquad := (mul_eq_zero.mp hH).resolve_left (pow_ne_zero 2 hdiff)
  refine ⟨R,hRm,hs,?_⟩
  nlinarith only [hquad]
#print axioms Paper7B4Analytic.three_disjoint_identity_perron_data

theorem three_disjoint_small_repeat_impossible (m R a c : ℕ)
    (hm2 : 2 ≤ m) (hm3 : m ≤ 3) (hRm : m < R) (hs : a+c = 2*m^2)
    (he : (R : ℝ)^4-(2*(m : ℝ)^2+4)*(R : ℝ)^2+(a : ℝ)*c+2 = 0) : False := by
  have hsR : (a : ℝ)+c = 2*(m : ℝ)^2 := by exact_mod_cast hs
  have hsquare := congrArg (fun x : ℝ => x^2) hsR
  have hac : (0 : ℝ) ≤ (a : ℝ)*c := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have ht : (0 : ℝ) < (R : ℝ)^2 := sq_pos_of_pos hRpos
  have hbound : (R : ℝ)^2 ≤ 2*(m : ℝ)^2+4 := by
    by_contra hh
    have hfactor : 0 < (R : ℝ)^2*((R : ℝ)^2-(2*(m : ℝ)^2+4)) :=
      mul_pos ht (by linarith)
    nlinarith only [he,hac,hfactor]
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
    nlinarith only [hsquare,he,sq_nonneg ((a : ℝ)-(c : ℝ))]
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
    nlinarith only [hsquare,he,sq_nonneg ((a : ℝ)-(c : ℝ))]
#print axioms Paper7B4Analytic.three_disjoint_small_repeat_impossible

theorem three_disjoint_no_repeated_ordinary_nat (a b c d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (hn : nOf 4 (threePDisjointP a b c) (threePDisjointQ d) ≤ 49)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d)))
    (m : ℕ) (hm : 2 ≤ m) :
    mult (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) m ≠ 2 := by
  intro hmult
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm3 : m ≤ 3 := by
    by_contra hh
    have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    exact repeated_ordinary_below_four _ _ hn m hm4 hmult
  have hid := (Paper7Lemma22Periodic.lemma22_ordinary_clause 4
    (threePDisjointP a b c) (threePDisjointQ d) (by decide) m
    (by linarith) (by linarith) (by linarith)).2.2.1.mp hmult
  obtain ⟨R,hRm,hs,he⟩ := three_disjoint_identity_perron_data a b c d m hb hd hm hm3 hid hG
  exact three_disjoint_small_repeat_impossible m R a c hm hm3 hRm hs he
#print axioms Paper7B4Analytic.three_disjoint_no_repeated_ordinary_nat

theorem three_disjoint_big_count_le_one (a b c d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (hn : nOf 4 (threePDisjointP a b c) (threePDisjointQ d) ≤ 49)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d)))
    (x : ℝ) (hx : 2 ≤ x) :
    (Bplus (SG 4 (threePDisjointP a b c) (threePDisjointQ d))).count x ≤ 1 := by
  have hclause := Paper7Lemma22Periodic.lemma22_ordinary_clause 4
    (threePDisjointP a b c) (threePDisjointQ d) (by decide) x
    (by linarith) (by linarith) (by linarith)
  have htwo := hclause.2.1
  have hm : mult (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) x ≤ 1 := by
    by_contra hh
    have hmult : mult (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) x = 2 := by omega
    have hmem : x ∈ spec (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) :=
      Multiset.count_pos.mp (by change 0 < mult _ x; omega)
    obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG x hmem
    have hz2 : (2 : ℤ) ≤ z := by rw [hz] at hx; exact_mod_cast hx
    have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have hzr : (z.toNat : ℝ) = x := by
      have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
      exact hc.trans hz.symm
    have hno := three_disjoint_no_repeated_ordinary_nat a b c d hb hd hn hG z.toNat (by omega)
    apply hno
    simpa only [hzr] using hmult
  simpa only [Bplus,Multiset.count_filter,hx,ite_true,mult] using hm
#print axioms Paper7B4Analytic.three_disjoint_big_count_le_one

end Paper7B4Analytic
