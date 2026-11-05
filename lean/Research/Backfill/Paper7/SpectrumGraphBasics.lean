import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Spectrum

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem adjMatrix_intCast {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : Type) [Ring K] :
    (G.adjMatrix ℤ).map (Int.castRingHom K) = G.adjMatrix K := by
  ext i j
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]

#print axioms Paper7Spectrum.adjMatrix_intCast

theorem graphPhi_map {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : Type) [CommRing K] :
    (graphPhi G).map (Int.castRingHom K) = (G.adjMatrix K).charpoly := by
  unfold graphPhi
  rw [← Matrix.charpoly_map]
  apply congrArg (fun A : Matrix V V K => A.charpoly)
  ext i j
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]

#print axioms Paper7Spectrum.graphPhi_map

theorem realAdjHermitian {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : (G.adjMatrix ℝ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix

#print axioms Paper7Spectrum.realAdjHermitian

theorem spec_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : (spec G).card = Fintype.card V := by
  change (G.adjMatrix ℝ).charpoly.roots.card = Fintype.card V
  calc
    (G.adjMatrix ℝ).charpoly.roots.card = (G.adjMatrix ℝ).charpoly.natDegree :=
      (realAdjHermitian G).splits_charpoly.natDegree_eq_card_roots.symm
    _ = Fintype.card V := (G.adjMatrix ℝ).charpoly_natDegree_eq_dim

#print axioms Paper7Spectrum.spec_card

end Paper7Spectrum
