import Research.Backfill.Paper7.B4PerronBounds

/-! NEW SOURCE ONLY. Exact ordinary-root equations when q vanishes and the
odd cycle positions have no pendants; all even coordinates remain arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped BigOperators Matrix Classical

theorem opposite_four_trace_formula (a b m : ℝ) (hm0 : m≠0) :
    (realFourProduct (m-a/m) m (m-b/m) m).trace =
      m^4-(a+b+4)*m^2+a*b+2*a+2*b+2 := by
  rw [real_four_trace]
  field_simp [hm0]; ring
#print axioms Paper7B4Analytic.opposite_four_trace_formula

theorem opposite_ordinary_spec_iff (p : Fin 4 → ℕ)
    (hp1 : p 1=0) (hp3 : p 3=0) (m : ℝ)
    (hmn : m≠-1) (hm0 : m≠0) (hm1 : m≠1) :
    m∈spec (SG 4 p (fun _ => 0)) ↔
      m^4-((p 0 : ℝ)+p 2+4)*m^2+(p 0 : ℝ)*p 2+2*(p 0 : ℝ)+2*(p 2 : ℝ)=0 := by
  have he : (Mono 4 p (fun _ => 0) m).trace =
      m^4-((p 0 : ℝ)+p 2+4)*m^2+(p 0 : ℝ)*p 2+2*(p 0 : ℝ)+2*(p 2 : ℝ)+2 := by
    rw [mono_four_product]
    simpa [fk,hp1,hp3] using opposite_four_trace_formula (p 0) (p 2) m hm0
  rw [← ordinary_trace_iff_spec p (fun _ => 0) m hmn hm0 hm1]
  constructor <;> intro h <;> linarith
#print axioms Paper7B4Analytic.opposite_ordinary_spec_iff

theorem positive_product_four_cases (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (h : u*v=4) :
    (u=1 ∧ v=4) ∨ (u=2 ∧ v=2) ∨ (u=4 ∧ v=1) := by
  by_cases hu1 : u=1
  · left
    rw [hu1] at h
    exact ⟨hu1,by omega⟩
  by_cases hu2 : u=2
  · right; left
    rw [hu2] at h
    exact ⟨hu2,by omega⟩
  have hu3 : 3 ≤ u := by omega
  have hv1 : v=1 := by
    by_contra hn
    have hv2 : 2 ≤ v := by omega
    have hh := Nat.mul_le_mul hu3 hv2
    omega
  right; right
  rw [hv1] at h
  exact ⟨by omega,hv1⟩
#print axioms Paper7B4Analytic.positive_product_four_cases

theorem opposite_perron_parameter_cases (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (hp1 : p 1=0) (hp3 : p 3=0) :
    ∃ R : ℕ, 3 ≤ R ∧
      ((p 0+3=R^2 ∧ p 2+6=R^2) ∨
        (p 0+4=R^2 ∧ p 2+4=R^2) ∨
        (p 0+6=R^2 ∧ p 2+3=R^2)) := by
  obtain ⟨R,hR,hmem,_hbound,hcap⟩ := integral_perron_load_data p (fun _ => 0) hp hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have he := (opposite_ordinary_spec_iff p hp1 hp3 R (by linarith) (by linarith)
    (by linarith)).mp hmem
  let u := R^2-p 0-2
  let v := R^2-p 2-2
  have hcap0 := hcap 0
  have hcap2 := hcap 2
  have hu : 0 < u := by dsimp [u]; omega
  have hv : 0 < v := by dsimp [v]; omega
  have huN : u+p 0+2=R^2 := by dsimp [u]; omega
  have hvN : v+p 2+2=R^2 := by dsimp [v]; omega
  have huR : (u : ℝ)+p 0+2=(R : ℝ)^2 := by exact_mod_cast huN
  have hvR : (v : ℝ)+p 2+2=(R : ℝ)^2 := by exact_mod_cast hvN
  have huv : u*v=4 := by
    have he4 : (R : ℝ)^4=((R : ℝ)^2)^2 := by ring
    have hu' : (u : ℝ)=(R : ℝ)^2-(p 0 : ℝ)-2 := by linarith
    have hv' : (v : ℝ)=(R : ℝ)^2-(p 2 : ℝ)-2 := by linarith
    have heR : (u : ℝ)*v=4 := by rw [hu',hv']; nlinarith only [he,he4]
    exact_mod_cast heR
  refine ⟨R,hR,?_⟩
  rcases positive_product_four_cases u v hu hv huv with ⟨h1,h4⟩ | ⟨h2,h2'⟩ | ⟨h4,h1⟩
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega,by omega⟩)
#print axioms Paper7B4Analytic.opposite_perron_parameter_cases

end Paper7B4Analytic
