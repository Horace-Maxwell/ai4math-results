import Research.Backfill.Paper7.IntroSubdividedArmLeafMoments
import Research.Backfill.Paper7.IntroBridgeCubicEntry

/-! Exact first, third and fifth entries along the actual leaf-middle-
attachment-cycle path, and its odd polynomial entry. Bridge status is needed
only at the attachment, never at the cycle endpoint. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroAttachmentMoments
open Matrix SimpleGraph Paper7IntroFourExternal Paper7IntroTerminalFourRemote

theorem subdivided_arm_cycle_short_entries
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l c : V)
    (hal : a ≠ l) (hcy : c ≠ y) (hac : G.Adj a c)
    (hbridge : ∀ v, G.Adj a v → G.IsBridge s(a, v))
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    (G.adjMatrix ℝ) l c = 0 ∧ ((G.adjMatrix ℝ) ^ 3) l c = 1 ∧
      ((G.adjMatrix ℝ) ^ 5) l c = (G.degree a : ℝ) + (G.degree c : ℝ) := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have h1 : A *ᵥ Pi.single l 1 = Pi.single y 1 := adjacency_single_one G l y hl
  have h2 : A ^ 2 *ᵥ Pi.single l 1 = Pi.single a 1 + Pi.single l 1 :=
    subdivided_arm_square_column G a y l hal hy hl
  have h3 : A ^ 3 *ᵥ Pi.single l 1 = A *ᵥ Pi.single a 1 + Pi.single y 1 := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, h1]
  have hcl3 : (A ^ 3) c l = 1 := by
    have hc := congrFun h3 c
    have hca : A c a = 1 := ite_eq_left hac.symm
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.add_apply,
      Pi.single_eq_of_ne hcy, hca, add_zero] using hc
  have hlc3 : (A ^ 3) l c = 1 := ((hA.pow 3).apply c l).trans hcl3
  have hlc : A l c = 0 := by
    change (if G.Adj l c then (1 : ℝ) else 0) = 0
    exact ite_eq_right (fun h => hcy ((hl c).mp h))
  have hac3 : (A ^ 3) a c = (G.degree a : ℝ) + (G.degree c : ℝ) - 1 :=
    bridge_vertex_cube_neighbor_entry G a hbridge c hac
  have hca3 : (A ^ 3) c a = (G.degree a : ℝ) + (G.degree c : ℝ) - 1 :=
    ((hA.pow 3).apply a c).trans hac3
  have h5 : A ^ 5 *ᵥ Pi.single l 1 =
      A ^ 3 *ᵥ Pi.single a 1 + A ^ 3 *ᵥ Pi.single l 1 := by
    rw [show A ^ 5 = A ^ 3 * A ^ 2 from pow_add A 3 2,
      ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add]
  have hcl5 : (A ^ 5) c l = (G.degree a : ℝ) + (G.degree c : ℝ) := by
    have hc := congrFun h5 c
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.add_apply,
      hca3, hcl3] at hc
    linarith
  exact ⟨hlc, hlc3, ((hA.pow 5).apply c l).trans hcl5⟩
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_cycle_short_entries

theorem subdivided_arm_cycle_odd_gap
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l c : V)
    (hal : a ≠ l) (hcy : c ≠ y) (hac : G.Adj a c)
    (hbridge : ∀ v, G.Adj a v → G.IsBridge s(a, v))
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    ((G.adjMatrix ℝ) ^ 5 - (5 : ℝ) • (G.adjMatrix ℝ) ^ 3 +
      (4 : ℝ) • G.adjMatrix ℝ) l c =
        (G.degree a : ℝ) + (G.degree c : ℝ) - 5 := by
  obtain ⟨h1, h3, h5⟩ := subdivided_arm_cycle_short_entries G a y l c hal hcy hac hbridge hy hl
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    h1, h3, h5]
  ring
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_cycle_odd_gap

end Paper7IntroAttachmentMoments
