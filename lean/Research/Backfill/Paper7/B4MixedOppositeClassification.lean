import Research.Backfill.Paper7.B4MixedOppositeRoots
import Research.Backfill.Paper7.B4OppositeClassification

/-! Source-only complete classification of the mixed opposite branch.
The second integer root is derived from the actual spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem mixed_opposite_second_root_integer (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (hG : IsIntegralGraph (SG 4 p q))
    (R d : ℕ) (hR : 3 ≤ R) (hd : d ≤ 5)
    (hadd : (q 0 : ℝ)+q 2+6 = 2*(R : ℝ)^2-d)
    (hmul : (q 0 : ℝ)*q 2+3*(q 0 : ℝ)+3*(q 2 : ℝ)+5 =
      (R : ℝ)^2*((R : ℝ)^2-d)) :
    ∃ S : ℕ, S^2+d = R^2 := by
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hdr : (d : ℝ) ≤ 5 := by exact_mod_cast hd
  have ht : 4 ≤ (R : ℝ)^2-d := by nlinarith
  let s : ℝ := Real.sqrt ((R : ℝ)^2-d)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = (R : ℝ)^2-d := Real.sq_sqrt (by linarith)
  have hs2 : 2 ≤ s := by nlinarith
  have he : s^4-((q 0 : ℝ)+q 2+6)*s^2+(q 0 : ℝ)*q 2+
      3*(q 0 : ℝ)+3*(q 2 : ℝ)+5 = 0 := by
    calc
      _ = (s^2-(R : ℝ)^2)*(s^2-((R : ℝ)^2-d)) := by
        have hh : s^4-((q 0 : ℝ)+q 2+6)*s^2+(q 0 : ℝ)*q 2+
            3*(q 0 : ℝ)+3*(q 2 : ℝ)+5 =
            s^4-((q 0 : ℝ)+q 2+6)*s^2+
              ((q 0 : ℝ)*q 2+3*(q 0 : ℝ)+3*(q 2 : ℝ)+5) := by ring
        rw [hh,hadd,hmul]
        ring
      _ = 0 := by rw [hsq]; ring
  have hmem := (mixed_opposite_ordinary_spec_iff p q hp0 hp1 hp2 hp3 hq1 hq3 s
    (by linarith) (by linarith) (by linarith)).mpr he
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p q) hG s hmem
  have hz0 : (0 : ℤ) ≤ z := by rw [hz] at hs0; exact_mod_cast hs0
  have hn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hnR : (z.toNat : ℝ) = s := by
    have hh : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hn
    exact hh.trans hz.symm
  refine ⟨z.toNat,?_⟩
  have hh : (z.toNat : ℝ)^2+d = (R : ℝ)^2 := by rw [hnR]; linarith
  exact_mod_cast hh
#print axioms Paper7B4Analytic.mixed_opposite_second_root_integer

theorem mixed_opposite_integral_parameters (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (hG : IsIntegralGraph (SG 4 p q)) :
    (q 0 = 5 ∧ q 2 = 2) ∨ (q 0 = 2 ∧ q 2 = 5) := by
  obtain ⟨R,hR,hcases⟩ :=
    mixed_opposite_perron_parameter_cases p q hp0 hp1 hp2 hp3 hq1 hq3 hG
  rcases hcases with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have haR : (q 0 : ℝ)+4 = (R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (q 2 : ℝ)+7 = (R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (q 0 : ℝ) = (R : ℝ)^2-4 := by linarith only [haR]
    have hb' : (q 2 : ℝ) = (R : ℝ)^2-7 := by linarith only [hbR]
    obtain ⟨S,hS⟩ := mixed_opposite_second_root_integer p q hp0 hp1 hp2 hp3 hq1 hq3 hG
      R 5 hR (by decide) (by norm_num; linarith)
      (by rw [ha',hb']; norm_num; ring)
    have hR3 := (square_gap_five R S hR hS).1
    left
    rw [hR3] at ha hb
    constructor <;> omega
  · have haR : (q 0 : ℝ)+5 = (R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (q 2 : ℝ)+5 = (R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (q 0 : ℝ) = (R : ℝ)^2-5 := by linarith only [haR]
    have hb' : (q 2 : ℝ) = (R : ℝ)^2-5 := by linarith only [hbR]
    obtain ⟨S,hS⟩ := mixed_opposite_second_root_integer p q hp0 hp1 hp2 hp3 hq1 hq3 hG
      R 4 hR (by decide) (by norm_num; linarith)
      (by rw [ha',hb']; norm_num; ring)
    exact False.elim (square_gap_four_impossible R S hR hS)
  · have haR : (q 0 : ℝ)+7 = (R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (q 2 : ℝ)+4 = (R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (q 0 : ℝ) = (R : ℝ)^2-7 := by linarith only [haR]
    have hb' : (q 2 : ℝ) = (R : ℝ)^2-4 := by linarith only [hbR]
    obtain ⟨S,hS⟩ := mixed_opposite_second_root_integer p q hp0 hp1 hp2 hp3 hq1 hq3 hG
      R 5 hR (by decide) (by norm_num; linarith)
      (by rw [ha',hb']; norm_num; ring)
    have hR3 := (square_gap_five R S hR hS).1
    right
    rw [hR3] at ha hb
    constructor <;> omega
#print axioms Paper7B4Analytic.mixed_opposite_integral_parameters

theorem mixed_opposite_parameters_named (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0)
    (hc : (q 0 = 5 ∧ q 2 = 2) ∨ (q 0 = 2 ∧ q 2 = 5)) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20a) := by
  rcases hc with ⟨hq0,hq2⟩ | ⟨hq0,hq2⟩
  · have hp : p = Paper7ThreeRepresentatives.g20aP := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g20aP,hp0,hp1,hp2,hp3]
    have hq : q = Paper7ThreeRepresentatives.g20aQ := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g20aQ,hq0,hq1,hq2,hq3]
    rw [hp,hq,← Paper7ThreeRepresentatives.g20a_parameters]
    exact ⟨.refl⟩
  · have hd : IsDihedral 4 (fun k : Fin 4 => k+2) := by
      refine ⟨2,Or.inl ?_⟩
      intro k
      fin_cases k <;> decide
    have hp : Paper7ThreeRepresentatives.g20aP = p ∘ (fun k : Fin 4 => k+2) := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g20aP,hp0,hp1,hp2,hp3]
    have hq : Paper7ThreeRepresentatives.g20aQ = q ∘ (fun k : Fin 4 => k+2) := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g20aQ,hq0,hq1,hq2,hq3]
    have hi := Paper7Setup.sg_iso_of_dihedral 4 p q
      Paper7ThreeRepresentatives.g20aP Paper7ThreeRepresentatives.g20aQ (by decide) _ hd hp hq
    rw [← Paper7ThreeRepresentatives.g20a_parameters]
    exact hi
#print axioms Paper7B4Analytic.mixed_opposite_parameters_named

theorem mixed_opposite_integral_iso_g20a (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (hG : IsIntegralGraph (SG 4 p q)) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20a) :=
  mixed_opposite_parameters_named p q hp0 hp1 hp2 hp3 hq1 hq3
    (mixed_opposite_integral_parameters p q hp0 hp1 hp2 hp3 hq1 hq3 hG)
#print axioms Paper7B4Analytic.mixed_opposite_integral_iso_g20a

theorem mixed_opposite_integral_iff_parameters (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) :
    IsIntegralGraph (SG 4 p q) ↔ (q 0 = 5 ∧ q 2 = 2) ∨ (q 0 = 2 ∧ q 2 = 5) := by
  constructor
  · intro hG
    exact mixed_opposite_integral_parameters p q hp0 hp1 hp2 hp3 hq1 hq3 hG
  · intro hc
    obtain ⟨e⟩ := mixed_opposite_parameters_named p q hp0 hp1 hp2 hp3 hq1 hq3 hc
    exact Paper7Normalize.graphIso_integral _ _ e.symm Paper7ControlB4.g20a_integral
#print axioms Paper7B4Analytic.mixed_opposite_integral_iff_parameters

end Paper7B4Analytic
