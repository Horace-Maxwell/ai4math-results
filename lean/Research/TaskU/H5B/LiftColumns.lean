import Research.TaskU.H5B.LiftBlock
import Research.TaskU.H5B.LiftData
import Research.TaskU.H5B.Seeds
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace TaskU.H5.Spectrum
open Finset Matrix
open Cyc5 (V)
open scoped BigOperators

def baseLift (s : Fin 5) (g : H) : ℤ :=
  (LiftData.baseData.getD s.val #[]).getD (25*g.a.val+5*g.b.val+g.c.val) 0

def minorWeight (s : Fin 5) (i : F) : V :=
  (LiftData.cofactorData.getD s.val #[]).getD i.val 0

def liftDir (s : Fin 5) (i : F) : V :=
  (LiftData.directionData.getD s.val #[]).getD i.val 0

theorem baseAug : ∀ (s : Fin 5) (a b : F),
    (∑ c : F, baseLift s ⟨a,b,c⟩) = seed s b a := by decide +kernel

def basisCol (i k : F) : V := if k=i then 1 else 0

def shortBlock (s : Fin 5) : Matrix F F V :=
  Matrix.of fun i j => (LiftData.blockData.getD s.val #[]).getD (5*i.val+j.val) 0

private def compactCheck (s : Fin 5) (i j : F) : Bool :=
  @decide _ (Cyc5.instDecidableEqV (coordBlock (baseLift s) i j) (shortBlock s i j))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem compact_entries : ∀ (s : Fin 5) (i j : F),
    coordBlock (baseLift s) i j = shortBlock s i j := by
  intro s i j
  exact of_decide_eq_true ((by decide +kernel : ∀ (s : Fin 5) (i j : F), compactCheck s i j = true) s i j)

theorem compact_matrix (s : Fin 5) : coordBlock (baseLift s) = shortBlock s := by
  ext i j : 1
  exact compact_entries s i j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem fixedTables : ∀ s : Fin 5,
    laplace 5 (shortBlock s) = 0 ∧
    (∀ i : F, laplace 5 ((shortBlock s).updateCol 0 (basisCol i)) =
       minorWeight s i) ∧
    (∑ i : F, minorWeight s i * liftDir s i) = 1 ∧
    (∀ i : F, (Cyc5.sumCoeff (minorWeight s i) : F) = 1) := by
  decide +kernel

theorem baseBlock_det (s : Fin 5) : (coordBlock (baseLift s)).det = 0 := by
  rw [compact_matrix, ← fiveLaplace]; exact (fixedTables s).1

theorem minorDir (s : Fin 5) : ∑ i : F, minorWeight s i * liftDir s i = 1 :=
  (fixedTables s).2.2.1

theorem minorResidue (s : Fin 5) (i : F) : (Cyc5.sumCoeff (minorWeight s i) : F) = 1 :=
  (fixedTables s).2.2.2 i

theorem det_first_column (s : Fin 5) (h : F → V) :
    ((coordBlock (baseLift s)).updateCol 0 h).det = ∑ i, h i * minorWeight s i := by
  let L := (LinearMap.proj (R := V) (φ := fun _ : F => V) 0).comp
    (Matrix.cramer (coordBlock (baseLift s)))
  change L h = _
  have split : h = ∑ i, h i • basisCol i := by
    funext j
    simp [basisCol, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [split,map_sum]
  apply sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  congr 1
  change ((coordBlock (baseLift s)).updateCol 0 (basisCol i)).det = _
  rw [compact_matrix, ← fiveLaplace]; exact (fixedTables s).2.1 i

end TaskU.H5.Spectrum
