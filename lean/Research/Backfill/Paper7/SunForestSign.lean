import Research.Backfill.Paper7.TridiagonalSignInertia
import Research.Backfill.Paper7.SunGraphAdjacency

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Cleared Paper7Inertia
open scoped Matrix

def sunVertexRoot (b : ℕ) (L : Fin b → List ℕ) : SunV b L → Fin b
  | Sum.inl k => k
  | Sum.inr a => a.1
#print axioms Paper7Comparison.sunVertexRoot

/-- Alternating level along the core path and then along each actual arm. -/
def sunVertexLevel (b : ℕ) (L : Fin b → List ℕ) : SunV b L → ℕ
  | Sum.inl k => k.val
  | Sum.inr a => a.1.val + a.2.2.val + 1
#print axioms Paper7Comparison.sunVertexLevel

theorem sun_forest_levels_adjacent (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (v w : SunV b L)
    (hv : sunVertexRoot b L v ∈ Xset b) (hw : sunVertexRoot b L w ∈ Xset b)
    (ha : (sunGraph b L).Adj v w) :
    sunVertexLevel b L v + 1 = sunVertexLevel b L w ∨
      sunVertexLevel b L w + 1 = sunVertexLevel b L v := by
  rcases v with i | ⟨k, j, a⟩ <;> rcases w with i' | ⟨k', j', a'⟩
  · have hc := (sun_cycle_adj_iff b L hb i i').mp ha
    exact (cycle_adj_on_Xset b hb i i' hv hw).mp hc
  · have h := (sun_root_arm_adj_iff b L i k' j' a').mp ha
    change i.val + 1 = k'.val + a'.val + 1 ∨
      k'.val + a'.val + 1 + 1 = i.val
    left
    have hk := congrArg Fin.val h.1
    omega
  · have h := (sun_arm_root_adj_iff b L i' k j a).mp ha
    change k.val + a.val + 1 + 1 = i'.val ∨
      i'.val + 1 = k.val + a.val + 1
    right
    have hk := congrArg Fin.val h.1
    omega
  · have h := (sun_arm_adj_iff b L k k' j j' a a').mp ha
    have hk : k.val = k'.val := congrArg Fin.val h.1
    change k.val + a.val + 1 + 1 = k'.val + a'.val + 1 ∨
      k'.val + a'.val + 1 + 1 = k.val + a.val + 1
    rcases h.2.2 with h | h <;> omega
#print axioms Paper7Comparison.sun_forest_levels_adjacent

theorem sun_forest_sign_edge (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (v w : SunV b L)
    (hv : sunVertexRoot b L v ∈ Xset b) (hw : sunVertexRoot b L w ∈ Xset b)
    (ha : (sunGraph b L).Adj v w) :
    (-1 : ℝ) ^ sunVertexLevel b L v * (-1 : ℝ) ^ sunVertexLevel b L w = -1 :=
  alternating_sign_neighbors _ _ (sun_forest_levels_adjacent b L hb v w hv hw ha)
#print axioms Paper7Comparison.sun_forest_sign_edge

def forestSignLinear (b : ℕ) (L : Fin b → List ℕ) :
    (SunV b L → ℝ) →ₗ[ℝ] (SunV b L → ℝ) where
  toFun x v := (-1 : ℝ) ^ sunVertexLevel b L v * x v
  map_add' x y := by
    funext v
    exact mul_add _ _ _
  map_smul' c x := by
    funext v
    change (-1 : ℝ) ^ sunVertexLevel b L v * (c * x v) =
      c * ((-1 : ℝ) ^ sunVertexLevel b L v * x v)
    ring
#print axioms Paper7Comparison.forestSignLinear

theorem forestSignLinear_apply (b : ℕ) (L : Fin b → List ℕ)
    (x : SunV b L → ℝ) (v : SunV b L) :
    forestSignLinear b L x v = (-1 : ℝ) ^ sunVertexLevel b L v * x v := rfl
#print axioms Paper7Comparison.forestSignLinear_apply

theorem forestSignLinear_involutive (b : ℕ) (L : Fin b → List ℕ) :
    Function.Involutive (forestSignLinear b L) := by
  intro x
  funext v
  simp only [forestSignLinear_apply, ← mul_assoc, alternating_sign_square, one_mul]
#print axioms Paper7Comparison.forestSignLinear_involutive

theorem forestSignLinear_injective (b : ℕ) (L : Fin b → List ℕ) :
    Function.Injective (forestSignLinear b L) :=
  (forestSignLinear_involutive b L).injective
#print axioms Paper7Comparison.forestSignLinear_injective

theorem forestSign_support (b : ℕ) (L : Fin b → List ℕ) (x : SunV b L → ℝ)
    (hx : ∀ v, sunVertexRoot b L v ∉ Xset b → x v = 0) :
    ∀ v, sunVertexRoot b L v ∉ Xset b → forestSignLinear b L x v = 0 := by
  intro v hv
  rw [forestSignLinear_apply, hx v hv, mul_zero]
#print axioms Paper7Comparison.forestSign_support

/-- The support hypothesis deletes the final root and its entire arm fibre.
It is essential for odd b: there is no assertion about the whole graph spectrum. -/
theorem forestSign_adj_quadratic (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (x : SunV b L → ℝ) (hx : ∀ v, sunVertexRoot b L v ∉ Xset b → x v = 0) :
    ((sunGraph b L).adjMatrix ℝ).toQuadraticForm' (forestSignLinear b L x) =
      -((sunGraph b L).adjMatrix ℝ).toQuadraticForm' x := by
  classical
  simp only [quadratic_apply, Matrix.dot_mulVec_eq_sum_sum]
  calc
    (∑ w, ∑ v, forestSignLinear b L x v * (sunGraph b L).adjMatrix ℝ v w *
        forestSignLinear b L x w) =
        ∑ w, ∑ v, -(x v * (sunGraph b L).adjMatrix ℝ v w * x w) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvX : sunVertexRoot b L v ∈ Xset b
      · by_cases hwX : sunVertexRoot b L w ∈ Xset b
        · by_cases ha : (sunGraph b L).Adj v w
          · have hs := sun_forest_sign_edge b L hb v w hvX hwX ha
            simp only [forestSignLinear_apply, SimpleGraph.adjMatrix_apply, ite_eq_left ha, mul_one]
            calc
              ((-1 : ℝ) ^ sunVertexLevel b L v * x v) *
                  ((-1 : ℝ) ^ sunVertexLevel b L w * x w) =
                  ((-1 : ℝ) ^ sunVertexLevel b L v *
                    (-1 : ℝ) ^ sunVertexLevel b L w) * (x v * x w) := by ring
              _ = -(x v * x w) := by rw [hs]; ring
          · simp [SimpleGraph.adjMatrix_apply, ha]
        · simp [forestSignLinear_apply, hx w hwX]
      · simp [forestSignLinear_apply, hx v hvX]
    _ = -(∑ w, ∑ v, x v * (sunGraph b L).adjMatrix ℝ v w * x w) := by
      simp only [Finset.sum_neg_distrib]
#print axioms Paper7Comparison.forestSign_adj_quadratic

theorem quadratic_sub_apply {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    (M-N).toQuadraticForm' x = M.toQuadraticForm' x - N.toQuadraticForm' x := by
  simp only [quadratic_apply, Matrix.sub_mulVec, dotProduct_sub]
#print axioms Paper7Comparison.quadratic_sub_apply

theorem forestSign_scalar_quadratic (b : ℕ) (L : Fin b → List ℕ)
    (m : ℝ) (x : SunV b L → ℝ) :
    (Matrix.scalar (SunV b L) m).toQuadraticForm' (forestSignLinear b L x) =
      (Matrix.scalar (SunV b L) m).toQuadraticForm' x := by
  rw [Matrix.scalar_apply, quadratic_diagonal]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, forestSignLinear_apply]
  apply Finset.sum_congr rfl
  intro v hv
  calc
    m * (((-1 : ℝ) ^ sunVertexLevel b L v * x v) *
        ((-1 : ℝ) ^ sunVertexLevel b L v * x v)) =
        ((-1 : ℝ) ^ sunVertexLevel b L v * (-1 : ℝ) ^ sunVertexLevel b L v) *
          (m * (x v * x v)) := by ring
    _ = m * (x v * x v) := by rw [alternating_sign_square, one_mul]
#print axioms Paper7Comparison.forestSign_scalar_quadratic

/-- A sign reversal for the two shifted graph forms on the actual supported subspace. -/
theorem forestSign_shift_quadratic (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (m : ℝ) (x : SunV b L → ℝ)
    (hx : ∀ v, sunVertexRoot b L v ∉ Xset b → x v = 0) :
    ((sunGraph b L).adjMatrix ℝ - Matrix.scalar (SunV b L) (-m)).toQuadraticForm'
        (forestSignLinear b L x) =
      -((sunGraph b L).adjMatrix ℝ - Matrix.scalar (SunV b L) m).toQuadraticForm' x := by
  rw [quadratic_sub_apply, forestSign_adj_quadratic b L hb x hx,
    forestSign_scalar_quadratic, map_neg, quadratic_neg_apply, quadratic_sub_apply]
  ring
#print axioms Paper7Comparison.forestSign_shift_quadratic

end Paper7Comparison
