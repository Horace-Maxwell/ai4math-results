import Research.TaskP.GeomSimplex.Packing

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

/-- The four affine barycentric numerators obtained by inverting T's augmented
vertex matrix. Their sum is 24. -/
def tcoords {R : Type*} [Ring R] (p : Fin 3 → R) : Fin 4 → R :=
  ![39 - 6*p 0 - 4*p 1 - 9*p 2, 6*p 0 + 4*p 1 - 3*p 2 - 3,
    6*p 0 - 4*p 1 + 9*p 2 - 15, -6*p 0 + 4*p 1 + 3*p 2 + 3]

theorem tcoords_mix (p q : Space 3) (a b : ℝ) (h : a + b = 1) (j : Fin 4) :
    tcoords (a • p + b • q) j = a * tcoords p j + b * tcoords q j := by
  fin_cases j <;> simp [tcoords] <;> nlinarith

theorem simplexT_facets (p : Space 3) :
    p ∈ simplex verticesT ↔ ∀ j, 0 ≤ tcoords p j := by
  constructor
  · have convex : Convex ℝ {x : Space 3 | ∀ j, 0 ≤ tcoords x j} := by
      intro x hx y hy a b ha hb hab j
      rw [tcoords_mix _ _ _ _ hab]
      exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
    apply convexHull_min _ convex
    rintro _ ⟨i, rfl⟩ j
    fin_cases i <;> fin_cases j <;> norm_num [verticesT, realPoint, tcoords]
  · intro h
    let w (j : Fin 4) := tcoords p j / 24
    apply mem_convexHull_of_exists_fintype w (realPoint ∘ verticesT)
    · intro j
      exact div_nonneg (h j) (by norm_num)
    · simp [w, tcoords, Fin.sum_univ_succ]
      ring
    · exact fun i => ⟨i, rfl⟩
    · ext j
      fin_cases j <;> simp [w, verticesT, tcoords, realPoint, Fin.sum_univ_succ] <;> ring

theorem simplexT_int (p : Lattice 3) :
    realPoint p ∈ simplex verticesT ↔ ∀ j, (0 : ℤ) ≤ tcoords p j := by
  rw [simplexT_facets]
  refine forall_congr' fun j => ?_
  fin_cases j <;> simp [tcoords, realPoint] <;> norm_cast

theorem fullT : fullSimplex verticesT := by
  rw [fullSimplex, affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h₀ := congrFun hv 0
  have h₁ := congrFun hv 1
  have h₂ := congrFun hv 2
  norm_num [Fin.sum_univ_succ, verticesT, realPoint] at hw h₀ h₁ h₂
  fin_cases i
  · change w 0 = 0
    linarith
  · change w 1 = 0
    linarith
  · change w 2 = 0
    linarith
  · change w 3 = 0
    linarith

def tpoints : Fin 8 → Lattice 3 :=
  ![![1,0,1], ![3,3,1], ![2,0,3], ![0,3,3], ![1,1,2], ![1,2,2], ![2,1,2], ![2,2,2]]

theorem points_of_T {p : Lattice 3} (hp : realPoint p ∈ simplex verticesT) :
    ∃ i : Fin 8, p = tpoints i := by
  have h := (simplexT_int p).mp hp
  have a := h 0
  have b := h 1
  have c := h 2
  have d := h 3
  norm_num [tcoords] at a b c d
  have corners :
      (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 3 ∧ p 1 = 3 ∧ p 2 = 1) ∨
      (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 3) ∨ (p 0 = 0 ∧ p 1 = 3 ∧ p 2 = 3) ∨
      (p 0 = 1 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 2) ∨
      (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 2 ∧ p 1 = 2 ∧ p 2 = 2) := by
    have hz₁ : 1 ≤ p 2 := by omega
    have hz₂ : p 2 ≤ 3 := by omega
    have hy₁ : 0 ≤ p 1 := by omega
    have hy₂ : p 1 ≤ 3 := by omega
    interval_cases hz : p 2 <;> interval_cases hy : p 1 <;> omega
  rcases corners with h | h | h | h | h | h | h | h
  · exact ⟨0, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨1, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨2, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨3, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨4, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨5, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨6, funext <| by intro j; fin_cases j <;> tauto⟩
  · exact ⟨7, funext <| by intro j; fin_cases j <;> tauto⟩

end TaskP.GeomSimplex.Proof
