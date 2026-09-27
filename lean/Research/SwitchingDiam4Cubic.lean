import Mathlib

/-!
# A total-reality lemma for the switching conjecture on trees of diameter ≤ 4

Session 2 of `work/round6/switching` (PROOF.md §9.9, class D1).  For a tree of diameter ≤ 4 in
class D1, the explicit switching `s⁺` fails at a secular eigenvalue `θ` only if
`θ ^ 3 - θ + 2 = 0` (because `G(θ) = θ + 2 / (θ ^ 2 - 1)` there).  This file proves that no
eigenvalue of a real symmetric matrix with rational entries satisfies that cubic, which is the
algebraic step ("all Galois conjugates of an eigenvalue are real, but `X³ - X + 2` has only one
real root").

Main result: `SwitchingDiam4.no_eigenvalue_root_cubic`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace SwitchingDiam4

/-- A real root of `x³ - x + 2` is `< -1`. -/
lemma real_root_lt (x : ℝ) (hx : x ^ 3 - x + 2 = 0) : x < -1 := by
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 1) (sq_nonneg (x - 1 / 2)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ x + 1) (sq_nonneg (x - 1)), sq_nonneg (x + 1)]

/-- `x³ - x + 2` has at most one real root. -/
lemma real_root_unique (x y : ℝ) (hx : x ^ 3 - x + 2 = 0) (hy : y ^ 3 - y + 2 = 0) :
    x = y := by
  have hx1 := real_root_lt x hx
  have hy1 := real_root_lt y hy
  have h : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · nlinarith [mul_pos (by linarith : (0 : ℝ) < -x) (by linarith : (0 : ℝ) < -y)]

/-- `x³ - x + 2` has no rational root. -/
lemma no_rat_root (r : ℚ) : r ^ 3 - r + 2 ≠ 0 := by
  intro hr
  -- first `r` is an integer (integral root theorem), then check integers directly
  have hmon : (X ^ 3 - X + 2 : ℤ[X]).Monic := by monicity!
  have hr' : aeval r (X ^ 3 - X + 2 : ℤ[X]) = 0 := by
    simp only [map_add, map_sub, map_pow, aeval_X, map_ofNat]; exact hr
  obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic hmon hr'
  rw [← hm] at hr
  have hz : (m : ℚ) ^ 3 - m + 2 = ((m ^ 3 - m + 2 : ℤ) : ℚ) := by push_cast; ring
  have hmz : m ^ 3 - m + 2 = 0 := by
    have : ((m ^ 3 - m + 2 : ℤ) : ℚ) = 0 := by
      rw [← hz]; simpa [algebraMap_int_eq] using hr
    exact_mod_cast this
  rcases le_or_gt m (-2) with h | h
  · nlinarith [sq_nonneg m, sq_nonneg (m + 2)]
  · nlinarith [sq_nonneg m, sq_nonneg (m + 1), sq_nonneg (m - 1)]

/-- **No eigenvalue of a real symmetric rational matrix is a root of `X³ - X + 2`.** -/
theorem no_eigenvalue_root_cubic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (hA : Aᵀ = A) (θ : ℝ)
    (hθ : ((A.map (algebraMap ℚ ℝ)).charpoly).eval θ = 0) :
    θ ^ 3 - θ + 2 ≠ 0 := by
  intro h3
  set p : ℚ[X] := X ^ 3 - X + 2 with hp
  have hpm : p.Monic := by rw [hp]; monicity!
  have hpdeg : p.natDegree = 3 := by rw [hp]; compute_degree!
  have hroots : p.roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem (fun r hr => ?_)
    rw [mem_roots hpm.ne_zero, IsRoot, hp] at hr
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_ofNat] at hr
    exact no_rat_root r hr
  have hirr : Irreducible p :=
    (hpm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).2 hroots
  have hpθ : aeval θ p = 0 := by
    rw [hp]; simp only [map_add, map_sub, map_pow, aeval_X, map_ofNat]; exact h3
  have hmin : p = minpoly ℚ θ := minpoly.eq_of_irreducible_of_monic hirr hpθ hpm
  have hc : aeval θ A.charpoly = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← charpoly_map]; exact hθ
  have hdvd : p ∣ A.charpoly := hmin ▸ minpoly.dvd ℚ θ hc
  have hdvdR : p.map (algebraMap ℚ ℝ) ∣ (A.map (algebraMap ℚ ℝ)).charpoly := by
    rw [charpoly_map]; exact Polynomial.map_dvd _ hdvd
  have hherm : (A.map (algebraMap ℚ ℝ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial, ← transpose_map, hA]
  have hsplit : (p.map (algebraMap ℚ ℝ)).Splits :=
    hherm.splits_charpoly.of_dvd (charpoly_monic _).ne_zero hdvdR
  have hmonR : (p.map (algebraMap ℚ ℝ)).Monic := hpm.map _
  have hdegR : (p.map (algebraMap ℚ ℝ)).natDegree = 3 := by
    rw [natDegree_map, hpdeg]
  have hcard : (p.map (algebraMap ℚ ℝ)).roots.card = 3 := by
    rw [splits_iff_card_roots.1 hsplit, hdegR]
  have hall : ∀ r ∈ (p.map (algebraMap ℚ ℝ)).roots, r = θ := by
    intro r hr
    rw [mem_roots hmonR.ne_zero, IsRoot, hp] at hr
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_ofNat, eval_add, eval_sub, eval_pow, eval_X, eval_ofNat] at hr
    exact real_root_unique r θ hr h3
  have hrep : (p.map (algebraMap ℚ ℝ)).roots = Multiset.replicate 3 θ := by
    rw [← hcard]; exact Multiset.eq_replicate_card.2 hall
  have hnext := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hmonR
  rw [hrep, Multiset.sum_replicate] at hnext
  have hn0 : (p.map (algebraMap ℚ ℝ)).nextCoeff = 0 := by
    rw [nextCoeff, hdegR]
    simp [hp, coeff_X]
  rw [hn0] at hnext
  have hθ0 : θ = 0 := by
    simp at hnext; linarith
  rw [hθ0] at h3
  norm_num at h3

end SwitchingDiam4

#print axioms SwitchingDiam4.no_rat_root
#print axioms SwitchingDiam4.real_root_unique
#print axioms SwitchingDiam4.no_eigenvalue_root_cubic
