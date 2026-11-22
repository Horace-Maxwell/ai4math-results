import Research.TaskP.GeomSimplex.Packing

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

/-- The four linear parts of the barycentric coordinates of U, multiplied by 18. -/
def uform {R : Type*} [Ring R] (p : Fin 3 → R) : Fin 4 → R :=
  ![-18 * p 2 - (18 * p 0 - 13 * p 1), 18 * p 0 - 13 * p 1,
    18 * p 2 - p 1, p 1]

def budget {R : Type*} [Ring R] (t : R) (j : Fin 4) : R := if j = 0 then 18 * t else 0

theorem forms_total {R : Type*} [CommRing R] (p : Fin 3 → R) :
    ∑ j, uform p j = 0 := by simp [uform, Fin.sum_univ_succ]; ring

theorem form_sum {R : Type*} [CommRing R] {k : ℕ} (v : Fin k → Fin 3 → R) (j : Fin 4) :
    uform (∑ i, v i) j = ∑ i, uform (v i) j := by
  fin_cases j <;> simp [uform, Finset.sum_apply, Finset.mul_sum, Finset.sum_sub_distrib]

theorem form_smul (v : Space 3) (a : ℝ) (j : Fin 4) :
    uform (a • v) j = a * uform v j := by
  fin_cases j <;> simp [uform] <;> ring

theorem form_add {R : Type*} [CommRing R] (p q : Fin 3 → R) (j : Fin 4) :
    uform (p + q) j = uform p j + uform q j := by
  fin_cases j <;> simp [uform] <;> ring

theorem cast_form (a : Lattice 3) (j : Fin 4) :
    uform (realPoint a) j = ((uform a j : ℤ) : ℝ) := by
  fin_cases j <;> norm_num [uform, realPoint]

theorem convex_facets (t : ℝ) : Convex ℝ {p : Space 3 | ∀ j, -budget t j ≤ uform p j} := by
  intro x hx y hy a b ha hb hab j
  rw [form_add, form_smul, form_smul]
  have hx' := mul_le_mul_of_nonneg_left (hx j) ha
  have hy' := mul_le_mul_of_nonneg_left (hy j) hb
  linarith [congrArg (fun r : ℝ => r * (-budget t j)) hab]

theorem simplexU_facets (p : Space 3) :
    p ∈ simplex verticesU ↔ ∀ j, -budget (1 : ℝ) j ≤ uform p j := by
  constructor
  · apply convexHull_min _ (convex_facets 1)
    rintro _ ⟨i, rfl⟩ j
    fin_cases i <;> fin_cases j <;> norm_num [verticesU, realPoint, budget, uform]
  · intro h
    let w (j : Fin 4) := (uform p j + budget (1 : ℝ) j) / 18
    apply mem_convexHull_of_exists_fintype w (realPoint ∘ verticesU)
    · intro j
      dsimp [w]
      linarith [h j]
    · simp [w, budget, uform, Fin.sum_univ_succ]
      ring
    · exact fun i => ⟨i, rfl⟩
    · ext j
      fin_cases j <;> simp [w, verticesU, uform, budget, realPoint, Fin.sum_univ_succ] <;> ring

theorem dilateU_facets (t : ℕ) (ht : 0 < t) (p : Space 3) :
    p ∈ dilate t (simplex verticesU) ↔ ∀ j, -budget (t : ℝ) j ≤ uform p j := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hbud (j : Fin 4) : budget (t : ℝ) j = (t : ℝ) * budget 1 j := by
    by_cases h : j = 0 <;> simp [budget, h]
    ring
  constructor
  · rintro ⟨q, hq, rfl⟩ j
    rw [form_smul, hbud, ← mul_neg]
    exact mul_le_mul_of_nonneg_left ((simplexU_facets q).1 hq j) ht'.le
  · intro hp
    refine ⟨(t : ℝ)⁻¹ • p, (simplexU_facets _).2 ?_, ?_⟩
    · intro j
      rw [form_smul, ← div_eq_inv_mul, le_div_iff₀ ht']
      simpa [hbud, mul_comm] using hp j
    · change (t : ℝ) • ((t : ℝ)⁻¹ • p) = p
      rw [smul_smul, mul_inv_cancel₀ ht'.ne', one_smul]

theorem dilateU_int (t : ℕ) (ht : 0 < t) (p : Lattice 3) :
    realPoint p ∈ dilate t (simplex verticesU) ↔ ∀ j, -budget (t : ℤ) j ≤ uform p j := by
  rw [dilateU_facets t ht]
  refine forall_congr' fun j => ?_
  rw [cast_form]
  by_cases h : j = 0 <;> simp [budget, h]
  norm_cast

theorem fullU : fullSimplex verticesU := by
  rw [fullSimplex, affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h₀ := congrFun hv 0
  have h₁ := congrFun hv 1
  have h₂ := congrFun hv 2
  norm_num [Fin.sum_univ_succ, verticesU, realPoint] at hw h₀ h₁ h₂
  fin_cases i
  · change w 0 = 0
    linarith
  · change w 1 = 0
    linarith
  · change w 2 = 0
    linarith
  · change w 3 = 0
    linarith

end TaskP.GeomSimplex.Proof
