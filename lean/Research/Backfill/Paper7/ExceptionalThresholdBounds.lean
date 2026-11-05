import Research.Backfill.Paper7.ExceptionalCoreLift
import Research.Backfill.Paper7.SunForestSign

/-! Both original exceptional-threshold inequalities, with the full Y.card
contribution and the actual original SunV graph. No full-cycle symmetry. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Exceptional
open BackfillPaper7.Challenge Paper7Comparison Paper7Inertia

theorem shifted_sun_isHermitian (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) m).IsHermitian := by
  rw [Matrix.scalar_apply]
  exact ((SG b p q).isHermitian_adjMatrix ℝ).sub (Matrix.isHermitian_diagonal _)
#print axioms Paper7Exceptional.shifted_sun_isHermitian

def exceptionalLift (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) :=
  (unitLift b p q Y hY).comp ((coreRootMap b Y).prod (coreAmplitudeMap b p Y))
#print axioms Paper7Exceptional.exceptionalLift

theorem exceptionalLift_injective (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) : Function.Injective (exceptionalLift b p q Y hY) := by
  intro v w h
  apply coreRootMap_injective b Y
  funext k
  exact congrFun h (Sum.inl k)
#print axioms Paper7Exceptional.exceptionalLift_injective

theorem exceptionalLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Kq b q ∩ Xset b)
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) 1).toQuadraticForm'
        (exceptionalLift b p q Y hY v) =
      (exceptionalDomainMatrix b p Y).toQuadraticForm' v :=
  (unitLift_quadratic b p q hb Y hY (coreRootMap b Y v) (coreAmplitudeMap b p Y v)).trans
    (core_amplitude_identity b p Y hb v)
#print axioms Paper7Exceptional.exceptionalLift_quadratic

theorem exceptionalLift_support (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    ∀ w, sunVertexRoot b (pq b p q) w ∉ Xset b → exceptionalLift b p q Y hY v w = 0 := by
  have hYX : Y ⊆ Xset b := fun k hk => (Finset.mem_inter.mp (hY hk)).2
  intro w hw
  rcases w with k | ⟨k, j, i⟩
  · exact coreRootMap_support b Y hYX v k hw
  · have hk : k ∉ Y := fun h => hw (hYX h)
    have hr := coreRootMap_support b Y hYX v k hw
    change unitArmValue b p q Y hY (coreRootMap b Y v) (coreAmplitudeMap b p Y v) k j = 0
    simp [unitArmValue, hk, hr]
#print axioms Paper7Exceptional.exceptionalLift_support

theorem exceptional_positive_core_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Kq b q ∩ Xset b) :
    Y.card + nPos (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1)) ≤ Ngt (SG b p q) 1 := by
  have h := nPos_map_le (exceptionalDomainMatrix b p Y)
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) 1)
    (exceptionalDomainMatrix_isHermitian b p Y) (shifted_sun_isHermitian b p q 1)
    (exceptionalLift b p q Y hY) (exceptionalLift_injective b p q Y hY)
    (fun v => (exceptionalLift_quadratic b p q hb Y hY v).symm.le)
  simpa only [exceptionalDomainMatrix_nPos, nPos_shift_eq_Ngt] using h
#print axioms Paper7Exceptional.exceptional_positive_core_bound

def exceptionalNegativeLift (b : ℕ) (p q : Fin b → ℕ) (Y : Finset (Fin b))
    (hY : Y ⊆ Kq b q ∩ Xset b) :
    ((Y ⊕ ↥(Xset b \ Y)) → ℝ) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) :=
  (forestSignLinear b (pq b p q)).comp (exceptionalLift b p q Y hY)
#print axioms Paper7Exceptional.exceptionalNegativeLift

theorem exceptionalNegativeLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Kq b q ∩ Xset b)
    (v : (Y ⊕ ↥(Xset b \ Y)) → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) (-1)).toQuadraticForm'
        (exceptionalNegativeLift b p q Y hY v) =
      -(exceptionalDomainMatrix b p Y).toQuadraticForm' v := by
  change ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) (-1)).toQuadraticForm'
    (forestSignLinear b (pq b p q) (exceptionalLift b p q Y hY v)) = _
  rw [forestSign_shift_quadratic b (pq b p q) hb 1 _
    (exceptionalLift_support b p q Y hY v), exceptionalLift_quadratic b p q hb Y hY v]
#print axioms Paper7Exceptional.exceptionalNegativeLift_quadratic

theorem exceptional_negative_core_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (hY : Y ⊆ Kq b q ∩ Xset b) :
    Y.card + nPos (tridiag (Xset b \ Y) (fun k => (p k : ℝ) - 1)) ≤ Nlt (SG b p q) (-1) := by
  have hi : Function.Injective (exceptionalNegativeLift b p q Y hY) :=
    (forestSignLinear_injective b (pq b p q)).comp (exceptionalLift_injective b p q Y hY)
  have h := nNeg_map_le (-(exceptionalDomainMatrix b p Y))
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) (-1))
    (exceptionalDomainMatrix_isHermitian b p Y).neg (shifted_sun_isHermitian b p q (-1))
    (exceptionalNegativeLift b p q Y hY) hi (fun v =>
      ((exceptionalNegativeLift_quadratic b p q hb Y hY v).trans
        (quadratic_neg_apply (exceptionalDomainMatrix b p Y) v).symm).le)
  simpa only [nNeg_neg _ (exceptionalDomainMatrix_isHermitian b p Y),
    exceptionalDomainMatrix_nPos, nNeg_shift_eq_Nlt] using h
#print axioms Paper7Exceptional.exceptional_negative_core_bound

/-- Exactly the two original exceptional inequalities for arbitrary admissible
Y and t, with no assumed inertia comparison or spectral symmetry. -/
theorem lemma51_exceptional (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (Y : Finset (Fin b)) (t : Fin b → ℝ) (hY : Y ⊆ Kq b q ∩ Xset b)
    (ht : ∀ k ∈ Xset b \ Y, t k ≤ (p k : ℝ) - 1) :
    Y.card + nPos (tridiag (Xset b \ Y) t) ≤ Ngt (SG b p q) 1 ∧
    Y.card + nPos (tridiag (Xset b \ Y) t) ≤ Nlt (SG b p q) (-1) := by
  have hc := Nat.add_le_add_left
    (tridiag_inertia_mono (Xset b \ Y) t (fun k => (p k : ℝ) - 1) ht).1 Y.card
  exact ⟨hc.trans (exceptional_positive_core_bound b p q hb Y hY),
    hc.trans (exceptional_negative_core_bound b p q hb Y hY)⟩
#print axioms Paper7Exceptional.lemma51_exceptional

end Paper7Exceptional
