import Research.Backfill.Paper7.IntroAttachmentCubicColumn
import Research.Backfill.Paper7.IntroBridgeCubicEntry

/-! The proved attachment cubic column and the actual bridge cubic entry
give the fourth and sixth diagonal moments by symmetric-column inner products. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroAttachmentMoments
open Matrix SimpleGraph Paper7IntroLocalQuartic Paper7IntroTerminalFourRemote

theorem symmetric_power_columns_dot
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (r s : ℕ) (i j : V) :
    (A ^ r *ᵥ Pi.single i 1) ⬝ᵥ (A ^ s *ᵥ Pi.single j 1) =
      (A ^ (r + s)) i j := by
  rw [pow_add, Matrix.mul_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  change (∑ k, (A ^ r) k i * (A ^ s) k j) = ∑ k, (A ^ r) i k * (A ^ s) k j
  apply Finset.sum_congr rfl
  intro k _
  rw [(hA.pow r).apply i k]
#print axioms Paper7IntroAttachmentMoments.symmetric_power_columns_dot

theorem subdivided_star_attachment_even_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (leaf : Y → V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hal : ∀ i : Y, a ≠ leaf i)
    (hNy : ∀ (i : Y) z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ (i : Y) z, G.Adj (leaf i) z ↔ z = i.val)
    (hbridge : ∀ v, G.Adj a v → G.IsBridge s(a, v)) :
    G.degree a = Y.card + 1 ∧
      ((G.adjMatrix ℝ) ^ 4) a a = (Y.card : ℝ) ^ 2 +
        3 * (Y.card : ℝ) + (G.degree c : ℝ) ∧
      ((G.adjMatrix ℝ) ^ 6) a a = ((G.adjMatrix ℝ) ^ 4) c c +
        (Y.card : ℝ) ^ 3 + 5 * (Y.card : ℝ) ^ 2 +
          3 * (Y.card : ℝ) + 2 * (Y.card : ℝ) * (G.degree c : ℝ) := by
  let A := G.adjMatrix ℝ
  let ea : V → ℝ := Pi.single a 1
  let ec : V → ℝ := Pi.single c 1
  let u : V → ℝ := A *ᵥ ea
  let v : V → ℝ := A ^ 2 *ᵥ ec
  let m : ℝ := Y.card
  let d : ℝ := G.degree c
  have hA : A.IsSymm := G.isSymm_adjMatrix
  obtain ⟨hdeg, hcol⟩ := subdivided_star_attachment_cubic_column G a c Y leaf hc hNa hal hNy hNl
  have hdegR : (G.degree a : ℝ) = m + 1 := by
    change (G.degree a : ℝ) = (Y.card : ℝ) + 1
    exact_mod_cast hdeg
  change A ^ 3 *ᵥ ea = v + (m + 1) • u - ec at hcol
  have hac : G.Adj a c := by
    apply (G.mem_neighborFinset a c).mp
    rw [hNa]
    exact Finset.mem_insert_self c Y
  have hca : A c a = 1 := ite_eq_left hac.symm
  have huu : u ⬝ᵥ u = m + 1 := by
    change (A *ᵥ Pi.single a 1) ⬝ᵥ (A *ᵥ Pi.single a 1) = _
    rw [← symmetric_square_diagonal A hA a]
    change ((G.adjMatrix ℝ) ^ 2) a a = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hdegR]
  have hvv : v ⬝ᵥ v = (A ^ 4) c c :=
    symmetric_power_columns_dot A hA 2 2 c c
  have huv : u ⬝ᵥ v = m + d := by
    calc
      u ⬝ᵥ v = (A ^ 3) a c := by
        simpa only [u, v, ea, ec, pow_one] using symmetric_power_columns_dot A hA 1 2 a c
      _ = m + d := by
        rw [bridge_vertex_cube_neighbor_entry G a hbridge c hac, hdegR]
        change m + 1 + d - 1 = m + d
        ring
  have hvu : v ⬝ᵥ u = m + d := by rw [dotProduct_comm]; exact huv
  have hec : ec ⬝ᵥ ec = 1 := by
    simp only [ec, single_dotProduct, one_mul, Pi.single_eq_same]
  have huec : u ⬝ᵥ ec = 1 := by
    simp only [u, ea, ec, dotProduct_single, mul_one, Matrix.mulVec_single_one,
      Matrix.col_apply, hca]
  have hecu : ec ⬝ᵥ u = 1 := by rw [dotProduct_comm]; exact huec
  have hvec : v ⬝ᵥ ec = d := by
    simp only [v, ec, dotProduct_single, mul_one, Matrix.mulVec_single_one, Matrix.col_apply]
    change ((G.adjMatrix ℝ) ^ 2) c c = (G.degree c : ℝ)
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hecv : ec ⬝ᵥ v = d := by rw [dotProduct_comm]; exact hvec
  have hm4 : (A ^ 4) a a = m ^ 2 + 3 * m + d := by
    calc
      (A ^ 4) a a = u ⬝ᵥ (A ^ 3 *ᵥ ea) := by
        symm
        simpa only [u, ea, pow_one] using symmetric_power_columns_dot A hA 1 3 a a
      _ = u ⬝ᵥ (v + (m + 1) • u - ec) := congrArg (fun z => u ⬝ᵥ z) hcol
      _ = m ^ 2 + 3 * m + d := by
        rw [dotProduct_sub, dotProduct_add, dotProduct_smul, huv, huu, huec]
        simp only [smul_eq_mul]
        ring
  have hm6 : (A ^ 6) a a = (A ^ 4) c c + m ^ 3 + 5 * m ^ 2 + 3 * m + 2 * m * d := by
    rw [show A ^ 6 = (A ^ 3) ^ 2 from pow_mul A 3 2,
      symmetric_square_diagonal (A ^ 3) (hA.pow 3) a]
    change (A ^ 3 *ᵥ ea) ⬝ᵥ (A ^ 3 *ᵥ ea) = _
    rw [hcol]
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hvv, huu, hec, huv, hvu, hvec, hecv, huec, hecu]
    ring
  exact ⟨hdeg, hm4, hm6⟩
#print axioms Paper7IntroAttachmentMoments.subdivided_star_attachment_even_moments

end Paper7IntroAttachmentMoments
