import Research.Backfill.Paper7.B4SinglePMixedPolynomial

/-! Source-only open-unit-root proof for one positive P site and Q disjoint
from that site. The case splits concern zero support and the value P=1 only. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic

theorem single_p_disjoint_small_root (a s b c : ℕ)
    (ha : 0 < a) (hq : 0 < s+c) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ singlePDisjointPolynomial a s b c t = 0 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  by_cases hb0 : b = 0
  · subst b
    by_cases hc0 : c = 0
    · subst c
      have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
      let f : ℝ → ℝ := fun t => t*(t-a)*(t-s-1)-(2*t-a)*(2*t-s-2)
      have hcont : Continuous f := by dsimp [f]; fun_prop
      have h0 : f 0 = -(a : ℝ)*((s : ℝ)+2) := by dsimp [f]; ring
      have h1 : f 1 = (s : ℝ) := by dsimp [f]; ring
      simp only [Nat.cast_zero]
      apply open_unit_root_of_factor (singlePDisjointPolynomial a s 0 0) f hcont
        (Or.inl ⟨by rw [h0]; nlinarith only [mul_pos haR (show 0 < (s : ℝ)+2 by linarith)],
          by rw [h1]; exact hspos⟩)
      intro t hf
      have he : singlePDisjointPolynomial a s 0 0 t = (t-1)^3*f t := by
        dsimp [singlePDisjointPolynomial,f]
        ring
      rw [he,hf,mul_zero]
    have hcpos : (0 : ℝ) < c := by exact_mod_cast (Nat.pos_of_ne_zero hc0)
    by_cases hs0 : s = 0
    · subst s
      let f : ℝ → ℝ := fun t => t*(t-a-2)*(t-c-1)-2*(t-1)*(t-a)
      have hcont : Continuous f := by dsimp [f]; fun_prop
      have h0 : f 0 = -2*(a : ℝ) := by dsimp [f]; ring
      have h1 : f 1 = (c : ℝ)*((a : ℝ)+1) := by dsimp [f]; ring
      simp only [Nat.cast_zero]
      apply open_unit_root_of_factor (singlePDisjointPolynomial a 0 0 c) f hcont
        (Or.inl ⟨by rw [h0]; linarith,by rw [h1]; exact mul_pos hcpos (by linarith)⟩)
      intro t hf
      have he : singlePDisjointPolynomial a 0 0 c t = (t-1)^3*f t := by
        dsimp [singlePDisjointPolynomial,f]
        ring
      rw [he,hf,mul_zero]
    have hspos : (0 : ℝ) < s := by exact_mod_cast (Nat.pos_of_ne_zero hs0)
    let f : ℝ → ℝ := fun t => t*(t-a)*(t-c-1)*(t-s-1)-
      ((t-1)*(t-a)+t*(t-c-1))*(2*t-s-2)
    have hcont : Continuous f := by dsimp [f]; fun_prop
    have h0 : f 0 = (a : ℝ)*((s : ℝ)+2) := by dsimp [f]; ring
    have h1 : f 1 = -(a : ℝ)*c*s := by dsimp [f]; ring
    simp only [Nat.cast_zero]
    apply open_unit_root_of_factor (singlePDisjointPolynomial a s 0 c) f hcont
      (Or.inr ⟨by rw [h0]; exact mul_pos haR (by linarith),
        by rw [h1]; nlinarith only [mul_pos (mul_pos haR hcpos) hspos]⟩)
    intro t hf
    have he : singlePDisjointPolynomial a s 0 c t = (t-1)^2*f t := by
      dsimp [singlePDisjointPolynomial,f]
      ring
    rw [he,hf,mul_zero]
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (Nat.pos_of_ne_zero hb0)
  by_cases hc0 : c = 0
  · subst c
    by_cases ha1 : a = 1
    · subst a
      let f : ℝ → ℝ := fun t => t*(t^2-((s : ℝ)+2)*t+b+s+1)-
        (2*t-1)*(2*t-s-2)
      have hcont : Continuous f := by dsimp [f]; fun_prop
      have h0 : f 0 = -(s : ℝ)-2 := by dsimp [f]; ring
      have h1 : f 1 = (b : ℝ)+s := by dsimp [f]; ring
      simp only [Nat.cast_zero,Nat.cast_one]
      apply open_unit_root_of_factor (singlePDisjointPolynomial 1 s b 0) f hcont
        (Or.inl ⟨by rw [h0]; linarith,by rw [h1]; linarith⟩)
      intro t hf
      have he : singlePDisjointPolynomial 1 s b 0 t = (t-1)^3*f t := by
        dsimp [singlePDisjointPolynomial,f]
        ring
      rw [he,hf,mul_zero]
    have ha2 : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    let f : ℝ → ℝ := fun t => t*(t-a)*(t^2-((s : ℝ)+2)*t+b+s+1)-
      (t-1)*(2*t-a)*(2*t-s-2)
    have hcont : Continuous f := by dsimp [f]; fun_prop
    have h0 : f 0 = (a : ℝ)*((s : ℝ)+2) := by dsimp [f]; ring
    have h1 : f 1 = (1-(a : ℝ))*b := by dsimp [f]; ring
    simp only [Nat.cast_zero]
    apply open_unit_root_of_factor (singlePDisjointPolynomial a s b 0) f hcont
      (Or.inr ⟨by rw [h0]; exact mul_pos haR (by linarith),
        by rw [h1]; exact mul_neg_of_neg_of_pos (by linarith) hbpos⟩)
    intro t hf
    have he : singlePDisjointPolynomial a s b 0 t = (t-1)^2*f t := by
      dsimp [singlePDisjointPolynomial,f]
      ring
    rw [he,hf,mul_zero]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (Nat.pos_of_ne_zero hc0)
  by_cases ha1 : a = 1
  · subst a
    let f : ℝ → ℝ := fun t => t*(t-c-1)*(t^2-((s : ℝ)+2)*t+b+s+1)-
      ((t-1)^2+t*(t-c-1))*(2*t-s-2)
    have hcont : Continuous f := by dsimp [f]; fun_prop
    have h0 : f 0 = (s : ℝ)+2 := by dsimp [f]; ring
    have h1 : f 1 = -(c : ℝ)*((b : ℝ)+s) := by dsimp [f]; ring
    simp only [Nat.cast_one]
    apply open_unit_root_of_factor (singlePDisjointPolynomial 1 s b c) f hcont
      (Or.inr ⟨by rw [h0]; linarith,
        by rw [h1]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith)⟩)
    intro t hf
    have he : singlePDisjointPolynomial 1 s b c t = (t-1)^2*f t := by
      dsimp [singlePDisjointPolynomial,f]
      ring
    rw [he,hf,mul_zero]
  have ha2 : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  let f : ℝ → ℝ := fun t => t*(t-a)*(t-c-1)*(t^2-((s : ℝ)+2)*t+b+s+1)-
    (t-1)*((t-1)*(t-a)+t*(t-c-1))*(2*t-s-2)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have h0 : f 0 = -(a : ℝ)*((s : ℝ)+2) := by dsimp [f]; ring
  have h1 : f 1 = ((a : ℝ)-1)*b*c := by dsimp [f]; ring
  apply open_unit_root_of_factor (singlePDisjointPolynomial a s b c) f hcont
    (Or.inl ⟨by rw [h0]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith),
      by rw [h1]; exact mul_pos (mul_pos (by linarith) hbpos) hcpos⟩)
  intro t hf
  have he : singlePDisjointPolynomial a s b c t = (t-1)*f t := by
    dsimp [singlePDisjointPolynomial,f]
    ring
  rw [he,hf,mul_zero]
#print axioms Paper7B4Analytic.single_p_disjoint_small_root

end Paper7B4Analytic
