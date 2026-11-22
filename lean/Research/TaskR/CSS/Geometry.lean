import Research.TaskR.CSS.Challenge

namespace TaskR.CSS.Geometry

open TaskR.CSS.Challenge Set
open scoped BigOperators

def total (x : Space) : ℝ := x 0 + x 1 + x 2 + x 3
noncomputable def slack (r : ℝ) (x : Space) : ℝ := (r - total x) / 6
noncomputable def coeff (r : ℝ) (x : Space) (i : Fin 4) : ℝ := x i + slack r x * embed weight i
def mix (r : ℝ) (b : Space) : Space := fun i => b i - (r - total b) * embed weight i

theorem total_mix (r : ℝ) (b : Space) : total (mix r b) = 6 * total b - 5 * r := by
  norm_num [total, mix, embed, weight]
  ring

theorem coeff_mix (r : ℝ) (b : Space) (i : Fin 4) : coeff r (mix r b) i = b i := by
  simp only [coeff, slack, total_mix, mix]
  ring

theorem mix_coeff (r : ℝ) (x : Space) : mix r (coeff r x) = x := by
  funext i
  fin_cases i <;> norm_num [mix, coeff, slack, total, embed, weight] <;> ring

theorem total_coeff (r : ℝ) (x : Space) : total (coeff r x) = r - slack r x := by
  norm_num [coeff, slack, total, embed, weight]
  ring

theorem mem_mix (b : Space) (hb : ∀ i, 0 ≤ b i) (h : total b ≤ 1) : mix 1 b ∈ P := by
  let pts : Fin 5 → Space := Fin.cons (embed (-weight)) (fun i => embed (e i))
  let weights : Fin 5 → ℝ := Fin.cons (1 - total b) b
  apply mem_convexHull_of_exists_fintype weights pts
  · exact Fin.cases (sub_nonneg.mpr h) hb
  · simp [weights, Fin.sum_univ_succ, total]
    ring
  · exact Fin.cases (mem_insert _ _) (fun i => mem_insert_of_mem _ (mem_range_self i))
  · ext i
    fin_cases i <;>
      norm_num [weights, pts, Fin.sum_univ_succ, Finset.sum_apply, mix, e, embed, weight, total,
        Pi.single_apply] <;> ring

theorem constraints {y : Space} (hy : y ∈ P) :
    0 ≤ slack 1 y ∧ ∀ i, 0 ≤ coeff 1 y i := by
  change y ∈ convexHull ℝ vertices at hy
  apply convexHull_min (t := {x | 0 ≤ slack 1 x ∧ ∀ i, 0 ≤ coeff 1 x i}) _ _ hy
  · rintro x (rfl | ⟨j,rfl⟩)
    · constructor
      · norm_num [slack, total, embed, weight]
      · intro i
        fin_cases i <;> norm_num [coeff, slack, total, embed, weight]
    · constructor
      · fin_cases j <;> norm_num [slack, total, embed, e, Pi.single_apply]
      · intro i
        fin_cases j <;> fin_cases i <;>
          norm_num [coeff, slack, total, embed, e, Pi.single_apply, weight]
  · rw [convex_iff_add_mem]
    rintro x ⟨hx, hx'⟩ y ⟨hy',hy''⟩ a b ha hb hab
    have hs : slack 1 (a • x + b • y) = a * slack 1 x + b * slack 1 y := by
      simp [slack, total]
      linarith only [hab]
    change 0 ≤ slack 1 (a • x + b • y) ∧ _
    constructor
    · rw [hs]
      positivity
    · intro i
      have he : coeff 1 (a • x + b • y) i = a * coeff 1 x i + b * coeff 1 y i := by
        simp [coeff, hs]
        ring
      rw [he]
      exact add_nonneg (mul_nonneg ha (hx' i)) (mul_nonneg hb (hy'' i))

theorem mem_of_constraints {y : Space} (hs : 0 ≤ slack 1 y) (hc : ∀ i, 0 ≤ coeff 1 y i) : y ∈ P := by
  rw [← mix_coeff 1 y]
  exact mem_mix _ hc (by rw [total_coeff]; linarith)

theorem nonHollow : NonHollow := by
  let S := {x : Space | 0 < slack 1 x} ∩ ⋂ i : Fin 4, {x : Space | 0 < coeff 1 x i}
  have hS : IsOpen S := by
    apply IsOpen.inter
    · apply isOpen_lt continuous_const
      unfold slack total
      fun_prop
    · apply isOpen_iInter_of_finite
      intro i
      apply isOpen_lt continuous_const
      unfold coeff slack total
      fun_prop
  apply interior_maximal (t := S) _ hS
  · constructor
    · norm_num [slack,total]
    · apply mem_iInter.mpr
      intro i
      fin_cases i <;> norm_num [coeff,slack,total, embed,weight]
  · intro y hy
    exact mem_of_constraints hy.1.le (fun i => (mem_iInter.mp hy.2 i).le)

end TaskR.CSS.Geometry
