import Research.Backfill.Paper1.PathAndSign
import Research.ICGGeneralBridge

/-!
This bridges the frozen simple-graph energy to the old Hermitian-matrix energy
before using the existing spectral
theorem. It does not define graph energy to be the target L1 expression.
The local dependencies PathAndSign and Additional have separate acceptance receipts.
Acceptance evidence for this module is recorded by check_noncorner_graph.py.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
-/

set_option autoImplicit false

namespace CodexPaper1

open BackfillPaper1

namespace GraphBridge

/-- The loop-removal in fromRel has no effect when n is excluded from D. -/
lemma icg_adj_iff (n : ℕ) (D : Finset ℕ) (hND : n ∉ D) (i j : Fin n) :
    (Challenge.icg n D).Adj i j ↔ Nat.gcd ((j - i : Fin n) : ℕ) n ∈ D := by
  unfold Challenge.icg
  rw [SimpleGraph.fromRel_adj]
  unfold Challenge.icgRel
  constructor
  · rintro ⟨_, h | h⟩
    · rwa [ICGBridge.gcd_sub_comm_fin n i j] at h
    · exact h
  · intro h
    refine ⟨?_, Or.inr h⟩
    rintro rfl
    apply hND
    rw [Fin.coe_sub_iff_le.mpr (show (i : ℕ) ≤ i from le_rfl)] at h
    simpa using h

lemma adjMatrix_eq (n : ℕ) (D : Finset ℕ) (hND : n ∉ D) :
    (Challenge.icg n D).adjMatrix ℝ = ICGBridge.icgAdj n D := by
  ext i j
  simp only [SimpleGraph.adjMatrix_apply, icg_adj_iff n D hND i j,
    ICGBridge.icgAdj, Matrix.of_apply]

/-- The same real matrix has the same spectral energy; proof witnesses are irrelevant. -/
lemma matrix_energy_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ICGBridge.energy A hA = ICGBridge.energy B hB := by
  subst B
  rfl

lemma graph_energy_eq (n : ℕ) (D : Finset ℕ) (hND : n ∉ D) :
    Challenge.energy n D =
      ICGBridge.energy (ICGBridge.icgAdj n D) (ICGBridge.icgAdj_isHermitian n D) := by
  change ICGBridge.energy ((Challenge.icg n D).adjMatrix ℝ)
      ((Challenge.icg n D).isHermitian_adjMatrix ℝ) = _
  exact matrix_energy_congr (adjMatrix_eq n D hND) _ _

end GraphBridge

/-- The complete frozen graph-spectral statement, including prime 2 and empty D. -/
theorem check_Proposition6 : Challenge.Proposition6 := by
  intro p q a b hp hq hpq _ha _hb D hD
  have hND : p ^ a * q ^ b ∉ D := by
    intro h
    exact Nat.self_notMem_properDivisors (hD h)
  rw [GraphBridge.graph_energy_eq (p ^ a * q ^ b) D hND,
    ICGGeneral.energy_icgAdj_pq p q a b hp hq hpq D]
  exact (PathAndSign.l1Mat_triple_eq_L1mat p q a b (Challenge.divMat p q D)).symm

#print axioms check_Proposition6

end CodexPaper1
