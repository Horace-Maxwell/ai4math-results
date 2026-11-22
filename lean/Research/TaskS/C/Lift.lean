import Research.TaskS.C.Coordinates

namespace TaskS.C

open Challenge Set
open scoped BigOperators

theorem scaled_combination {d : ℕ} (v : Fin (d+1) → Space d) (β a : Fin (d+1) → ℝ)
    (hβ : ∀ i, 0 < β i) (hs : ∑ i, β i = 1) (hz : ∑ i, β i • v i = 0)
    (ha : ∀ i, 0 ≤ a i) {r : ℝ} (hr : 0 < r) (hbound : ∑ i, a i ≤ r) :
    ∃ y ∈ simplex v, r • y = ∑ i, a i • v i := by
  let s := r - ∑ i, a i
  let w := fun i => (a i + s * β i) / r
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg
    (add_nonneg (ha i) (mul_nonneg (sub_nonneg.mpr hbound) (hβ i).le)) hr.le
  have hw₁ : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one, s]
    rw [add_sub_cancel, div_self hr.ne']
  refine ⟨∑ i, w i • v i, (convex_convexHull ℝ (range v)).sum_mem
    (fun i _ => hw i) hw₁ (fun i _ => subset_convexHull ℝ _ (mem_range_self i)), ?_⟩
  rw [Finset.smul_sum]
  calc
    _ = ∑ i, (a i • v i + s • (β i • v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, show r * w i = a i + s * β i by dsimp [w]; field_simp,
        add_smul, smul_smul]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.smul_sum, hz, smul_zero, add_zero]

theorem rounded_cover {d : ℕ} (u : Fin (d+1) → Challenge.Lattice d) (ω β : Fin (d+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hβ : ∀ i, 0 < β i) (hs : ∑ i, β i = 1)
    (hz : ∑ i, β i • vertices u ω i = 0)
    (hspan : ∀ y : Space d, ∃ a : Fin (d+1) → ℝ, ∑ i, a i • vertices u ω i = y)
    (q : Fin (d+1) → ℕ) (hq : ∑ i, (q i : ℝ) • embed (u i) = 0)
    {r : ℝ} (hr : 0 < r) (hround : ∀ x : Fin (d+1) → ℝ, ∃ t : ℝ,
      (∑ i, (1 / ω i) * Int.fract (x i + (q i : ℝ)*t)) ≤ r) :
    Covers (simplex (vertices u ω)) r := by
  intro y
  obtain ⟨b, hb⟩ := hspan y
  let x := fun i => b i * ω i
  have hx : ∑ i, x i • embed (u i) = y := by simpa [x, vertices, smul_smul] using hb
  obtain ⟨t, ht⟩ := hround x
  let θ := fun i => x i + (q i : ℝ) * t
  let a := fun i => (1 / ω i) * Int.fract (θ i)
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (one_div_pos.mpr (hω i)).le (Int.fract_nonneg _)
  obtain ⟨p, hp, hrep⟩ := scaled_combination (vertices u ω) β a hβ hs hz ha hr ht
  let z : Challenge.Lattice d := fun k => ∑ i, ⌊θ i⌋ * u i k
  refine ⟨z, p, hp, ?_⟩
  rw [hrep, ← hx]
  ext k
  have hqk := congrFun hq k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hqk
  simp only [Pi.add_apply, Challenge.embed, z, Int.cast_sum, Int.cast_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vertices, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, (x i * (u i k : ℝ) + t * ((q i : ℝ) * (u i k : ℝ))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      change _ = _ + t * (∑ i, (q i : ℝ) * embed (u i) k)
      rw [hqk, mul_zero, add_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a, θ]
      rw [Int.fract]
      field_simp [(hω i).ne']
      ring

end TaskS.C
