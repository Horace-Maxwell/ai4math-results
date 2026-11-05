import Research.Backfill.Paper7.Lemma21FullSupport
import Research.Backfill.Paper7.SunSchurInertia

/-! Both exceptional inequalities on full Kq and the original R/R' index. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators
namespace Paper7Lemma21
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

def fullExceptionalLift (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    (FullCoreV b q → ℝ) →ₗ[ℝ] (SunV b (pq b p q) → ℝ) :=
  (signedLift b p q ε).comp ((fullRootMap b q).prod (fullAmplitude b p q ε))
#print axioms Paper7Lemma21.fullExceptionalLift

theorem fullExceptionalLift_injective (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    Function.Injective (fullExceptionalLift b p q ε) := by
  intro v w h
  apply fullRootMap_injective b q
  funext k
  exact congrFun h (Sum.inl k)
#print axioms Paper7Lemma21.fullExceptionalLift_injective

theorem fullExceptionalLift_quadratic (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hε : ε ^ 2 = 1) (v : FullCoreV b q → ℝ) :
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) ε).toQuadraticForm'
      (fullExceptionalLift b p q ε v) = (fullDomain b p q ε).toQuadraticForm' v := by
  change ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) ε).toQuadraticForm'
    (signedLift b p q ε (fullRootMap b q v, fullAmplitude b p q ε v)) = _
  rw [signedLift_quadratic b p q hb ε hε, fullAmplitude_identity]
#print axioms Paper7Lemma21.fullExceptionalLift_quadratic

theorem lemma21_exceptional (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    (Kq b q).card + nPos (Rmat b p q) ≤ Ngt (SG b p q) 1 ∧
    (Kq b q).card + nNeg (R'mat b p q) ≤ Nlt (SG b p q) (-1) := by
  have hp := nPos_map_le (fullDomain b p q 1)
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) 1)
    (fullDomain_isHermitian b p q 1) (shifted_adj_isHermitian _ _)
    (fullExceptionalLift b p q 1) (fullExceptionalLift_injective b p q 1)
    (fun v => (fullExceptionalLift_quadratic b p q hb 1 (by norm_num) v).symm.le)
  have hn := nNeg_map_le (fullDomain b p q (-1))
    ((SG b p q).adjMatrix ℝ - Matrix.scalar (SunV b (pq b p q)) (-1))
    (fullDomain_isHermitian b p q (-1)) (shifted_adj_isHermitian _ _)
    (fullExceptionalLift b p q (-1)) (fullExceptionalLift_injective b p q (-1))
    (fun v => (fullExceptionalLift_quadratic b p q hb (-1) (by norm_num) v).le)
  rw [(fullDomain_inertia b p q).1, nPos_shift_eq_Ngt] at hp
  rw [(fullDomain_inertia b p q).2, nNeg_shift_eq_Nlt] at hn
  exact ⟨hp,hn⟩
#print axioms Paper7Lemma21.lemma21_exceptional

end Paper7Lemma21
