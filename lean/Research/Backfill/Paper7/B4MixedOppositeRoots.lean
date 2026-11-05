import Research.Backfill.Paper7.B4OppositeRootEquations

/-! Source-only spectral reduction for the mixed opposite branch:
p=(0,1,0,1), q=(a,0,b,0), with arbitrary nonnegative a and b. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem mixed_opposite_trace_formula (a b m : ℝ)
    (hm0 : m ≠ 0) (hmden : m^2-1 ≠ 0) :
    (realFourProduct (m-a*m/(m^2-1)) (m-1/m)
      (m-b*m/(m^2-1)) (m-1/m)).trace =
      m^4-(a+b+6)*m^2+a*b+3*a+3*b+7 := by
  rw [real_four_trace]
  field_simp [hm0,hmden]
  ring
#print axioms Paper7B4Analytic.mixed_opposite_trace_formula

theorem mixed_opposite_ordinary_spec_iff (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p q) ↔
      m^4-((q 0 : ℝ)+q 2+6)*m^2+(q 0 : ℝ)*q 2+3*(q 0 : ℝ)+3*(q 2 : ℝ)+5 = 0 := by
  have hmden : m^2-1 ≠ 0 := by
    intro h
    have hprod : (m-1)*(m+1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hprod with hpos | hneg
    · exact hm1 (by linarith only [hpos])
    · exact hmn (by linarith only [hneg])
  have he : (Mono 4 p q m).trace =
      m^4-((q 0 : ℝ)+q 2+6)*m^2+(q 0 : ℝ)*q 2+3*(q 0 : ℝ)+3*(q 2 : ℝ)+7 := by
    rw [mono_four_product]
    simpa [fk,hp0,hp1,hp2,hp3,hq1,hq3] using
      mixed_opposite_trace_formula (q 0) (q 2) m hm0 hmden
  rw [← ordinary_trace_iff_spec p q m hmn hm0 hm1]
  constructor <;> intro h <;> linarith only [he,h]
#print axioms Paper7B4Analytic.mixed_opposite_ordinary_spec_iff

theorem mixed_opposite_perron_parameter_cases (p q : Fin 4 → ℕ)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 0) (hp3 : p 3 = 1)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (hG : IsIntegralGraph (SG 4 p q)) :
    ∃ R : ℕ, 3 ≤ R ∧
      ((q 0+4 = R^2 ∧ q 2+7 = R^2) ∨
        (q 0+5 = R^2 ∧ q 2+5 = R^2) ∨
        (q 0+7 = R^2 ∧ q 2+4 = R^2)) := by
  have hp : 0 < ∑ k, (p k+q k) := by
    have hle : p 1+q 1 ≤ ∑ k, (p k+q k) :=
      Finset.single_le_sum (f := fun k : Fin 4 => p k+q k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (1 : Fin 4))
    have hsite : 0 < p 1+q 1 := by omega
    exact hsite.trans_le hle
  obtain ⟨R,hR,hmem,_hbound,hcap⟩ := integral_perron_load_data p q hp hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have he := (mixed_opposite_ordinary_spec_iff p q hp0 hp1 hp2 hp3 hq1 hq3 R
    (by linarith) (by linarith) (by linarith)).mp hmem
  let u := R^2-q 0-3
  let v := R^2-q 2-3
  have hcap0 : q 0+3 ≤ R^2 := by simpa [hp0] using hcap 0
  have hcap2 : q 2+3 ≤ R^2 := by simpa [hp2] using hcap 2
  have huN : u+q 0+3 = R^2 := by dsimp [u]; omega
  have hvN : v+q 2+3 = R^2 := by dsimp [v]; omega
  have huR : (u : ℝ)+q 0+3 = (R : ℝ)^2 := by exact_mod_cast huN
  have hvR : (v : ℝ)+q 2+3 = (R : ℝ)^2 := by exact_mod_cast hvN
  have huv : u*v = 4 := by
    have hu' : (u : ℝ) = (R : ℝ)^2-(q 0 : ℝ)-3 := by linarith only [huR]
    have hv' : (v : ℝ) = (R : ℝ)^2-(q 2 : ℝ)-3 := by linarith only [hvR]
    have heR : (u : ℝ)*v = 4 := by
      rw [hu',hv']
      nlinarith only [he]
    exact_mod_cast heR
  have hu : 0 < u := by
    by_contra hh
    have hz : u = 0 := by omega
    rw [hz,zero_mul] at huv
    omega
  have hv : 0 < v := by
    by_contra hh
    have hz : v = 0 := by omega
    rw [hz,mul_zero] at huv
    omega
  refine ⟨R,hR,?_⟩
  rcases positive_product_four_cases u v hu hv huv with ⟨h1,h4⟩ | ⟨h2,h2'⟩ | ⟨h4,h1⟩
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega,by omega⟩)
#print axioms Paper7B4Analytic.mixed_opposite_perron_parameter_cases

end Paper7B4Analytic
