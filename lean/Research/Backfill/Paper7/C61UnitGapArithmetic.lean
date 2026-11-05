import Research.Backfill.Paper7.C61ThreeQpositiveAlgebra

/-! NEW SOURCE ONLY. Natural-coordinate Dirichlet gap equations are solved
by sign and product inequalities. No bounded parameter search is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open Paper7C61Three

theorem unit_gap_two_cases (u v : ℕ)
    (h : (1-(u : ℝ))*(1-(v : ℝ))=1) :
    (u=0 ∧ v=0) ∨ (u=2 ∧ v=2) := by
  by_cases hu : u=0
  · left
    refine ⟨hu, ?_⟩
    have hv : (v : ℝ)=0 := by norm_num [hu] at h; exact_mod_cast h
    exact_mod_cast hv
  by_cases hv : v=0
  · have huR : (u : ℝ)=0 := by norm_num [hv] at h; exact_mod_cast h
    exact (hu (by exact_mod_cast huR)).elim
  have hu1 : 1≤u := by omega
  have hv1 : 1≤v := by omega
  have hm : ((u-1 : ℕ) : ℝ)*((v-1 : ℕ) : ℝ)=1 := by
    rw [Nat.cast_sub hu1, Nat.cast_sub hv1]
    push_cast
    nlinarith only [h]
  obtain ⟨ha,hb⟩ := natural_product_one (u-1) (v-1) hm
  exact Or.inr ⟨by omega,by omega⟩
#print axioms Paper7C61Four.unit_gap_two_cases

theorem unit_gap_zero_endpoint (d e : ℕ)
    (h : (d : ℝ)*((e : ℝ)-1)=1) : d=1 ∧ e=2 := by
  have hd0 : (0 : ℝ)≤d := Nat.cast_nonneg d
  have he2 : 2≤e := by
    by_contra hn
    have he1 : (e : ℝ)≤1 := by exact_mod_cast (show e≤1 by omega)
    have hm := mul_nonpos_of_nonneg_of_nonpos hd0 (show (e : ℝ)-1≤0 by linarith)
    linarith
  have hm : (d : ℝ)*((e-1 : ℕ) : ℝ)=1 := by
    simpa only [Nat.cast_sub (show 1≤e by omega),Nat.cast_one] using h
  obtain ⟨hd,he⟩ := natural_product_one d (e-1) hm
  exact ⟨hd,by omega⟩
#print axioms Paper7C61Four.unit_gap_zero_endpoint

theorem unit_gap_three_cases (c d e : ℕ)
    (h : ((c : ℝ)-1)*((d : ℝ)-1)*((e : ℝ)-1)=
      ((c : ℝ)-1)+((e : ℝ)-1)) :
    (c=1 ∧ e=1) ∨ (c=3 ∧ d=2 ∧ e=3) ∨
      (c=2 ∧ d=3 ∧ e=2) ∨ (c=0 ∧ d=1 ∧ e=2) ∨
      (c=2 ∧ d=1 ∧ e=0) := by
  by_cases hc0 : c=0
  · obtain ⟨hd,he⟩ := unit_gap_zero_endpoint d e (by norm_num [hc0] at h; nlinarith only [h])
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc0,hd,he⟩)))
  by_cases he0 : e=0
  · obtain ⟨hd,hc⟩ := unit_gap_zero_endpoint d c (by norm_num [he0] at h; nlinarith only [h])
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hc,hd,he0⟩)))
  by_cases hc1 : c=1
  · have heR : (e : ℝ)=1 := by norm_num [hc1] at h; linarith
    exact Or.inl ⟨hc1,by exact_mod_cast heR⟩
  by_cases he1 : e=1
  · have hcR : (c : ℝ)=1 := by norm_num [he1] at h; linarith
    exact Or.inl ⟨by exact_mod_cast hcR,he1⟩
  have hc2 : (2 : ℝ)≤c := by exact_mod_cast (show 2≤c by omega)
  have he2 : (2 : ℝ)≤e := by exact_mod_cast (show 2≤e by omega)
  have hce := mul_nonneg (show (0 : ℝ)≤(c : ℝ)-2 by linarith)
    (show (0 : ℝ)≤(e : ℝ)-2 by linarith)
  have hm : (1 : ℝ)≤((c : ℝ)-1)*((e : ℝ)-1) := by nlinarith only [hc2,he2,hce]
  have hd2 : 2≤d := by
    by_contra hn
    have hd1 : (d : ℝ)≤1 := by exact_mod_cast (show d≤1 by omega)
    have hh := mul_nonpos_of_nonneg_of_nonpos (by linarith :
      (0 : ℝ)≤((c : ℝ)-1)*((e : ℝ)-1)) (show (d : ℝ)-1≤0 by linarith)
    nlinarith only [h,hc2,he2,hh]
  have hd3 : d≤3 := by
    by_contra hn
    have hd4 : (4 : ℝ)≤d := by exact_mod_cast (show 4≤d by omega)
    have hh := mul_nonneg (by linarith : (0 : ℝ)≤((c : ℝ)-1)*((e : ℝ)-1))
      (show (0 : ℝ)≤(d : ℝ)-4 by linarith)
    nlinarith only [h,hc2,he2,hce,hm,hh]
  have hd : d=2 ∨ d=3 := by omega
  rcases hd with hd | hd
  · have hc3 : 3≤c := by
      by_contra hn
      have hc : c=2 := by omega
      norm_num [hc,hd] at h
    have he3 : 3≤e := by
      by_contra hn
      have he : e=2 := by omega
      norm_num [he,hd] at h
    have hprod : ((c-2 : ℕ) : ℝ)*((e-2 : ℕ) : ℝ)=1 := by
      rw [Nat.cast_sub (show 2≤c by omega),Nat.cast_sub (show 2≤e by omega)]
      push_cast
      norm_num [hd] at h
      nlinarith only [h]
    obtain ⟨hc,he⟩ := natural_product_one (c-2) (e-2) hprod
    exact Or.inr (Or.inl ⟨by omega,hd,by omega⟩)
  · have hcR : (c : ℝ)=2 := by norm_num [hd] at h; nlinarith only [h,hce,hc2,he2]
    have heR : (e : ℝ)=2 := by norm_num [hd] at h; nlinarith only [h,hce,hc2,he2]
    exact Or.inr (Or.inr (Or.inl ⟨by exact_mod_cast hcR,hd,by exact_mod_cast heR⟩))
#print axioms Paper7C61Four.unit_gap_three_cases

end Paper7C61Four
