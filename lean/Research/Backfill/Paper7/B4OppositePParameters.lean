import Research.Backfill.Paper7.B4OppositePDisjointRank
import Research.Backfill.Paper7.B4OppositePCubicExclusion

/-! Source-only complete classification of disjoint opposite P support.
The root and coefficient hypotheses used in the arithmetic are derived here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem opposite_one_q_nonintegral (a c b : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hnot : ¬ (a = 1 ∧ c = 1))
    (hn : nOf 4 (oppositeP a c) (oppositeQ b 0) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 (oppositeP a c) (oppositeQ b 0)) := by
  intro hG
  let p := oppositeP a c
  let q := oppositeQ b 0
  have hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1 :=
    disjoint_opposite_multiplicity_le_one p q ha rfl rfl rfl rfl hn hG
  have hd := opposite_unit_delta_zero_one_q a c b ha hc hb hnot
  have ho := opposite_positive_card_offset a c b 0 ha hc hG
  have hK : Kq 4 q = {1} := by ext i; fin_cases i <;> simp [Kq,q,oppositeQ,hb]
  have hcard : (Bplus (SG 4 p q)).card = 3 := by
    change (Bplus (SG 4 p q)).card+deltaE 4 p q 1 = 2+(Kq 4 q).card at ho
    rw [hd,hK] at ho
    norm_num at ho
    exact ho
  let T : ℤ := a+c+b+5
  let E : ℤ := a*c+((a : ℤ)+c)*(b+3)+2*b+4
  let D : ℤ := a*c*(b+1)+((a : ℤ)+c)*(b+2)
  apply opposite_spectral_cubic_impossible p q hn hG hm hcard T E D ((b : ℤ)+1)
  · dsimp [T,E,D]
    ring
  · intro m hm2 hmem
    have hH := (disjoint_opposite_ordinary_spec_iff p q rfl rfl rfl rfl m
      (by linarith) (by linarith) (by linarith)).mp hmem
    have hfac : disjointOppositeQuartic a c b 0 (m^2) = (m^2-1)*
        (m^6-(T : ℝ)*m^4+(E : ℝ)*m^2-D) := by
      dsimp [T,E,D,disjointOppositeQuartic]
      push_cast
      ring
    change disjointOppositeQuartic a c b (0 : ℕ) (m^2) = 0 at hH
    rw [Nat.cast_zero] at hH
    rw [hfac] at hH
    exact (mul_eq_zero.mp hH).resolve_left (by nlinarith)
#print axioms Paper7B4Analytic.opposite_one_q_nonintegral

theorem opposite_one_unit_p_nonintegral (c b d : ℕ)
    (hc : 0 < c) (hc1 : c ≠ 1) (hb : 0 < b) (hd : 0 < d)
    (hn : nOf 4 (oppositeP 1 c) (oppositeQ b d) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 (oppositeP 1 c) (oppositeQ b d)) := by
  intro hG
  let p := oppositeP 1 c
  let q := oppositeQ b d
  have hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1 :=
    disjoint_opposite_multiplicity_le_one p q (by norm_num [p,oppositeP])
      rfl rfl rfl rfl hn hG
  have hdelta := opposite_unit_delta_one c b d hc1 hb hd
  have ho := opposite_positive_card_offset 1 c b d (by omega) hc hG
  have hK : Kq 4 q = {1,3} := by ext i; fin_cases i <;> simp [Kq,q,oppositeQ,hb,hd]
  have hcard : (Bplus (SG 4 p q)).card = 3 := by
    change (Bplus (SG 4 p q)).card+deltaE 4 p q 1 = 2+(Kq 4 q).card at ho
    rw [hdelta,hK] at ho
    norm_num at ho
    omega
  let T : ℤ := c+b+d+6
  let E : ℤ := b*d+3*((b : ℤ)+d)+7+c*((b : ℤ)+d)+4*c
  let D : ℤ := c*b*d+2*c*((b : ℤ)+d)+3*c+b+d+2
  apply opposite_spectral_cubic_impossible p q hn hG hm hcard T E D c
  · dsimp [T,E,D]
    ring
  · intro m hm2 hmem
    have hH := (disjoint_opposite_ordinary_spec_iff p q rfl rfl rfl rfl m
      (by linarith) (by linarith) (by linarith)).mp hmem
    have hfac : disjointOppositeQuartic 1 c b d (m^2) = (m^2-1)*
        (m^6-(T : ℝ)*m^4+(E : ℝ)*m^2-D) := by
      dsimp [T,E,D,disjointOppositeQuartic]
      push_cast
      ring
    change disjointOppositeQuartic (1 : ℕ) c b d (m^2) = 0 at hH
    rw [Nat.cast_one] at hH
    rw [hfac] at hH
    exact (mul_eq_zero.mp hH).resolve_left (by nlinarith)
#print axioms Paper7B4Analytic.opposite_one_unit_p_nonintegral

theorem opposite_no_unit_p_nonintegral (a c b d : ℕ)
    (ha : 0 < a) (hc : 0 < c) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hb : 0 < b) (hd : 0 < d)
    (hn : nOf 4 (oppositeP a c) (oppositeQ b d) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 (oppositeP a c) (oppositeQ b d)) := by
  intro hG
  let p := oppositeP a c
  let q := oppositeQ b d
  have hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1 :=
    disjoint_opposite_multiplicity_le_one p q ha rfl rfl rfl rfl hn hG
  have hdelta := opposite_unit_delta_zero_two_q a c b d ha1 hc1 hb hd
  have ho := opposite_positive_card_offset a c b d ha hc hG
  have hK : Kq 4 q = {1,3} := by ext i; fin_cases i <;> simp [Kq,q,oppositeQ,hb,hd]
  have hcard : (Bplus (SG 4 p q)).card = 4 := by
    change (Bplus (SG 4 p q)).card+deltaE 4 p q 1 = 2+(Kq 4 q).card at ho
    rw [hdelta,hK] at ho
    norm_num at ho
    exact ho
  have hbound := simple_positive_card_lt_four p q hn hG hm
  omega
#print axioms Paper7B4Analytic.opposite_no_unit_p_nonintegral

theorem opposite_parameters_swap_integral (a c b d : ℕ)
    (hG : IsIntegralGraph (SG 4 (oppositeP a c) (oppositeQ b d))) :
    IsIntegralGraph (SG 4 (oppositeP c a) (oppositeQ d b)) := by
  have hd : IsDihedral 4 (fun k : Fin 4 => k+2) := by
    refine ⟨2,Or.inl ?_⟩
    intro k
    fin_cases k <;> decide
  have hp : oppositeP c a = oppositeP a c ∘ (fun k : Fin 4 => k+2) := by
    funext i
    fin_cases i <;> simp [oppositeP]
  have hq : oppositeQ d b = oppositeQ b d ∘ (fun k : Fin 4 => k+2) := by
    funext i
    fin_cases i <;> simp [oppositeQ]
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 (oppositeP a c) (oppositeQ b d)
    (oppositeP c a) (oppositeQ d b) (by decide) (fun k : Fin 4 => k+2) hd hp hq
  exact Paper7Normalize.graphIso_integral _ _ e hG
#print axioms Paper7B4Analytic.opposite_parameters_swap_integral

theorem opposite_disjoint_integral_parameters (a c b d : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hq : 0 < b+d)
    (hn : nOf 4 (oppositeP a c) (oppositeQ b d) ≤ 49)
    (hG : IsIntegralGraph (SG 4 (oppositeP a c) (oppositeQ b d))) : a = 1 ∧ c = 1 := by
  by_contra hnot
  have hn' : nOf 4 (oppositeP c a) (oppositeQ d b) ≤ 49 := by
    simp only [nOf,Fin.sum_univ_four] at hn ⊢
    change 4+(c+0+a+0)+2*(0+d+0+b) ≤ 49
    change 4+(a+0+c+0)+2*(0+b+0+d) ≤ 49 at hn
    omega
  have hG' := opposite_parameters_swap_integral a c b d hG
  by_cases hb : b = 0
  · subst b
    exact opposite_one_q_nonintegral c a d hc ha (by omega)
      (by intro hh; exact hnot ⟨hh.2,hh.1⟩) hn' hG'
  by_cases hd : d = 0
  · subst d
    exact opposite_one_q_nonintegral a c b ha hc (by omega) hnot hn hG
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  by_cases ha1 : a = 1
  · subst a
    exact opposite_one_unit_p_nonintegral c b d hc (by tauto) hbpos hdpos hn hG
  by_cases hc1 : c = 1
  · subst c
    exact opposite_one_unit_p_nonintegral a d b ha ha1 hdpos hbpos hn' hG'
  exact opposite_no_unit_p_nonintegral a c b d ha hc ha1 hc1 hbpos hdpos hn hG
#print axioms Paper7B4Analytic.opposite_disjoint_integral_parameters

end Paper7B4Analytic
