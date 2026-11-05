import Research.Backfill.Paper7.IntroRadiusThreeProjectorAlgebra

/-! The actual seven-root annihilator already gives AT=S and AS=9T.
Left multiplication yields A²S=9S. The exact true-leaf row and symmetry
of AS then transport the S diagonal to its unique neighbor. No Perron
vector, numerical moment, rank, or diagonal identity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroSLeafTransport
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroProjectors

theorem integral_radius_three_S_square_relation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) :
    (G.adjMatrix ℝ) ^ 2 * radiusThreeS (G.adjMatrix ℝ) =
      (9 : ℝ) • radiusThreeS (G.adjMatrix ℝ) := by
  obtain ⟨hAT, hAS⟩ := radiusThreeST_adj_relations G hI hbound
  rw [pow_two, mul_assoc, hAS, Matrix.mul_smul, hAT]
#print axioms Paper7IntroSLeafTransport.integral_radius_three_S_square_relation

theorem integral_radius_three_S_leaf_neighbor_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (l a : V) (hl : ∀ z, G.Adj l z ↔ z = a) :
    radiusThreeS (G.adjMatrix ℝ) a a =
      9 * radiusThreeS (G.adjMatrix ℝ) l l := by
  let A := G.adjMatrix ℝ
  let S := radiusThreeS A
  have hn : G.neighborFinset l = {a} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact hl z
  have hrow (M : Matrix V V ℝ) (j : V) : (A * M) l j = M a j := by
    change (G.adjMatrix ℝ *ᵥ (fun v => M v j)) l = M a j
    rw [G.adjMatrix_mulVec_apply, hn, Finset.sum_singleton]
  have hASsym : (A * S).IsSymm := by
    change (G.adjMatrix ℝ * radiusThreeS (G.adjMatrix ℝ)).IsSymm
    rw [(radiusThreeST_adj_relations G hI hbound).2]
    exact ((radiusThreeST_symmetric (G.adjMatrix ℝ) G.isSymm_adjMatrix).2).smul 9
  have hdiag : (A ^ 2 * S) l l = S a a := by
    calc
      (A ^ 2 * S) l l = (A * (A * S)) l l := by rw [pow_two, mul_assoc]
      _ = (A * S) a l := hrow (A * S) l
      _ = (A * S) l a := hASsym.apply l a
      _ = S a a := hrow S a
  have hBS : A ^ 2 * S = (9 : ℝ) • S :=
    integral_radius_three_S_square_relation G hI hbound
  have h := congrArg (fun M : Matrix V V ℝ => M l l) hBS
  change (A ^ 2 * S) l l = 9 * S l l at h
  rw [hdiag] at h
  exact h
#print axioms Paper7IntroSLeafTransport.integral_radius_three_S_leaf_neighbor_diagonal

end Paper7IntroSLeafTransport
