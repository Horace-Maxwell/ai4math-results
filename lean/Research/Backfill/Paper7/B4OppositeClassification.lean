import Research.Backfill.Paper7.B4OppositeRootEquations
import Research.Backfill.Paper7.ControlB4Representatives

/-! NEW SOURCE ONLY. A complete original-parameter branch: q is zero and
pendants occur at most at two opposite cycle vertices. The second ordinary
root is obtained from the transfer equation, not postulated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem square_gap_five (R S : ℕ) (hR : 3 ≤ R) (he : S^2+5=R^2) : R=3 ∧ S=2 := by
  have hlt : S < R := by nlinarith
  have hstep := Nat.pow_le_pow_left (show S+1 ≤ R by omega) 2
  have hS : S ≤ 2 := by nlinarith
  have hSsq := Nat.pow_le_pow_left hS 2
  have hR' : R ≤ 3 := by nlinarith
  exact ⟨by omega,by nlinarith⟩
#print axioms Paper7B4Analytic.square_gap_five

theorem square_gap_four_impossible (R S : ℕ) (hR : 3 ≤ R) : S^2+4≠R^2 := by
  intro he
  have hlt : S < R := by nlinarith
  have hstep := Nat.pow_le_pow_left (show S+1 ≤ R by omega) 2
  have hS : S ≤ 1 := by nlinarith
  have hSsq := Nat.pow_le_pow_left hS 2
  nlinarith
#print axioms Paper7B4Analytic.square_gap_four_impossible

theorem opposite_second_root_integer (p : Fin 4 → ℕ)
    (hp1 : p 1=0) (hp3 : p 3=0) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (R d : ℕ) (hR : 3 ≤ R) (hd : d ≤ 5)
    (hadd : (p 0 : ℝ)+p 2+4=2*(R : ℝ)^2-d)
    (hmul : (p 0 : ℝ)*p 2+2*(p 0 : ℝ)+2*(p 2 : ℝ)=
      (R : ℝ)^2*((R : ℝ)^2-d)) :
    ∃ S : ℕ, S^2+d=R^2 := by
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hdr : (d : ℝ) ≤ 5 := by exact_mod_cast hd
  have ht : 4 ≤ (R : ℝ)^2-d := by nlinarith
  let s : ℝ := Real.sqrt ((R : ℝ)^2-d)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2=(R : ℝ)^2-d := Real.sq_sqrt (by linarith)
  have hs2 : 2 ≤ s := by nlinarith
  have he : s^4-((p 0 : ℝ)+p 2+4)*s^2+(p 0 : ℝ)*p 2+
      2*(p 0 : ℝ)+2*(p 2 : ℝ)=0 := by
    calc
      _ = (s^2-(R : ℝ)^2)*(s^2-((R : ℝ)^2-d)) := by
        have hh : s^4-((p 0 : ℝ)+p 2+4)*s^2+(p 0 : ℝ)*p 2+
            2*(p 0 : ℝ)+2*(p 2 : ℝ)=
            s^4-((p 0 : ℝ)+p 2+4)*s^2+
              ((p 0 : ℝ)*p 2+2*(p 0 : ℝ)+2*(p 2 : ℝ)) := by ring
        rw [hh,hadd,hmul]
        ring
      _ = 0 := by rw [hsq]; ring
  have hmem := (opposite_ordinary_spec_iff p hp1 hp3 s (by linarith) (by linarith)
    (by linarith)).mpr he
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p (fun _ => 0)) hG s hmem
  have hz0 : (0 : ℤ) ≤ z := by rw [hz] at hs0; exact_mod_cast hs0
  have hn : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz0
  have hnR : (z.toNat : ℝ)=s := by
    have hh : (z.toNat : ℝ)=(z : ℝ) := by exact_mod_cast hn
    exact hh.trans hz.symm
  refine ⟨z.toNat,?_⟩
  have hh : (z.toNat : ℝ)^2+d=(R : ℝ)^2 := by rw [hnR]; linarith
  exact_mod_cast hh
#print axioms Paper7B4Analytic.opposite_second_root_integer

theorem opposite_integral_parameters (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (hp1 : p 1=0) (hp3 : p 3=0) :
    (p 0=6 ∧ p 2=3) ∨ (p 0=3 ∧ p 2=6) := by
  obtain ⟨R,hR,hcases⟩ := opposite_perron_parameter_cases p hp hG hp1 hp3
  rcases hcases with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have haR : (p 0 : ℝ)+3=(R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (p 2 : ℝ)+6=(R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (p 0 : ℝ)=(R : ℝ)^2-3 := by linarith
    have hb' : (p 2 : ℝ)=(R : ℝ)^2-6 := by linarith
    obtain ⟨S,hS⟩ := opposite_second_root_integer p hp1 hp3 hG R 5 hR (by decide)
      (by norm_num; linarith) (by rw [ha',hb']; norm_num; ring)
    have hR3 := (square_gap_five R S hR hS).1
    left
    rw [hR3] at ha hb
    constructor <;> omega
  · have haR : (p 0 : ℝ)+4=(R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (p 2 : ℝ)+4=(R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (p 0 : ℝ)=(R : ℝ)^2-4 := by linarith
    have hb' : (p 2 : ℝ)=(R : ℝ)^2-4 := by linarith
    obtain ⟨S,hS⟩ := opposite_second_root_integer p hp1 hp3 hG R 4 hR (by decide)
      (by norm_num; linarith) (by rw [ha',hb']; norm_num; ring)
    exact False.elim (square_gap_four_impossible R S hR hS)
  · have haR : (p 0 : ℝ)+6=(R : ℝ)^2 := by exact_mod_cast ha
    have hbR : (p 2 : ℝ)+3=(R : ℝ)^2 := by exact_mod_cast hb
    have ha' : (p 0 : ℝ)=(R : ℝ)^2-6 := by linarith
    have hb' : (p 2 : ℝ)=(R : ℝ)^2-3 := by linarith
    obtain ⟨S,hS⟩ := opposite_second_root_integer p hp1 hp3 hG R 5 hR (by decide)
      (by norm_num; linarith) (by rw [ha',hb']; norm_num; ring)
    have hR3 := (square_gap_five R S hR hS).1
    right
    rw [hR3] at ha hb
    constructor <;> omega
#print axioms Paper7B4Analytic.opposite_integral_parameters

theorem opposite_integral_iso_g13 (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (hp1 : p 1=0) (hp3 : p 3=0) :
    Nonempty (SG 4 p (fun _ => 0) ≃g sunGraph 4 G13) := by
  have hz : (fun _ : Fin 4 => (0 : ℕ))=Paper7ThreeRepresentatives.g13Q := by
    funext k
    fin_cases k <;> rfl
  rcases opposite_integral_parameters p hp hG hp1 hp3 with ⟨hp0,hp2⟩ | ⟨hp0,hp2⟩
  · have he : p=Paper7ThreeRepresentatives.g13P := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g13P,hp0,hp1,hp2,hp3]
    rw [he,hz,← Paper7ThreeRepresentatives.g13_parameters]
    exact ⟨.refl⟩
  · have hd : IsDihedral 4 (fun k : Fin 4 => k+2) := by
      refine ⟨2,Or.inl ?_⟩
      intro k
      fin_cases k <;> decide
    have he : Paper7ThreeRepresentatives.g13P=p ∘ (fun k : Fin 4 => k+2) := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g13P,hp0,hp1,hp2,hp3]
    have hq : Paper7ThreeRepresentatives.g13Q=(fun _ : Fin 4 => (0 : ℕ)) ∘
        (fun k : Fin 4 => k+2) := by
      funext k
      fin_cases k <;> rfl
    have hi := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
      Paper7ThreeRepresentatives.g13P Paper7ThreeRepresentatives.g13Q (by decide) _ hd he hq
    rw [← Paper7ThreeRepresentatives.g13_parameters]
    exact hi
#print axioms Paper7B4Analytic.opposite_integral_iso_g13

theorem opposite_integral_iff_parameters (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hp1 : p 1=0) (hp3 : p 3=0) :
    IsIntegralGraph (SG 4 p (fun _ => 0)) ↔
      (p 0=6 ∧ p 2=3) ∨ (p 0=3 ∧ p 2=6) := by
  constructor
  · intro hG
    exact opposite_integral_parameters p hp hG hp1 hp3
  · intro hc
    have hz : (fun _ : Fin 4 => (0 : ℕ))=Paper7ThreeRepresentatives.g13Q := by
      funext k
      fin_cases k <;> rfl
    rcases hc with ⟨hp0,hp2⟩ | ⟨hp0,hp2⟩
    · have he : p=Paper7ThreeRepresentatives.g13P := by
        funext k
        fin_cases k <;> simp [Paper7ThreeRepresentatives.g13P,hp0,hp1,hp2,hp3]
      have hi := Paper7ControlB4.g13_integral
      rw [← Paper7ThreeRepresentatives.g13_parameters] at hi
      rw [he,hz]
      exact hi
    · have hd : IsDihedral 4 (fun k : Fin 4 => k+2) := by
        refine ⟨2,Or.inl ?_⟩
        intro k
        fin_cases k <;> decide
      have he : Paper7ThreeRepresentatives.g13P=p ∘ (fun k : Fin 4 => k+2) := by
        funext k
        fin_cases k <;> simp [Paper7ThreeRepresentatives.g13P,hp0,hp1,hp2,hp3]
      have hq : Paper7ThreeRepresentatives.g13Q=(fun _ : Fin 4 => (0 : ℕ)) ∘
          (fun k : Fin 4 => k+2) := by
        funext k
        fin_cases k <;> rfl
      obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
        Paper7ThreeRepresentatives.g13P Paper7ThreeRepresentatives.g13Q (by decide) _ hd he hq
      have hi : IsIntegralGraph
          (SG 4 Paper7ThreeRepresentatives.g13P Paper7ThreeRepresentatives.g13Q) := by
        have hnamed := Paper7ControlB4.g13_integral
        rw [← Paper7ThreeRepresentatives.g13_parameters] at hnamed
        exact hnamed
      exact Paper7Normalize.graphIso_integral _ _ e.symm hi
#print axioms Paper7B4Analytic.opposite_integral_iff_parameters

end Paper7B4Analytic
