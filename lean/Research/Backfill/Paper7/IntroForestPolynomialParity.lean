import Research.Backfill.Paper7.GraphPhiCharpoly
import Mathlib

/-! Characteristic-polynomial parity for arbitrary finite two-colored graphs
and forests, including an empty forest. No restriction on branching is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddForest
open SimpleGraph Polynomial BackfillPaper7.Challenge.Legacy.Algebra

def twoColorSign (a : Fin 2) : ℤ := if a = 0 then 1 else -1
#print axioms Paper7IntroOddForest.twoColorSign

theorem twoColorSign_mul_self (a : Fin 2) :
    twoColorSign a * twoColorSign a = 1 := by
  fin_cases a <;> norm_num [twoColorSign]
#print axioms Paper7IntroOddForest.twoColorSign_mul_self

theorem twoColorSign_mul_of_ne (a b : Fin 2) (h : a ≠ b) :
    twoColorSign a * twoColorSign b = -1 := by
  have hc : ∀ a b : Fin 2, a ≠ b → twoColorSign a * twoColorSign b = -1 := by
    decide +kernel
  exact hc a b h
#print axioms Paper7IntroOddForest.twoColorSign_mul_of_ne

theorem twoColor_diagonal_involutive {V : Type} [Fintype V] [DecidableEq V]
    (c : V → Fin 2) :
    Matrix.diagonal (fun v => twoColorSign (c v)) *
      Matrix.diagonal (fun v => twoColorSign (c v)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [twoColorSign_mul_self, Matrix.diagonal_one]
#print axioms Paper7IntroOddForest.twoColor_diagonal_involutive

theorem twoColor_adjacency_conjugation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) :
    Matrix.diagonal (fun v => twoColorSign (c v)) * G.adjMatrix ℤ *
      Matrix.diagonal (fun v => twoColorSign (c v)) = -G.adjMatrix ℤ := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases h : G.Adj i j
  · simpa only [SimpleGraph.adjMatrix_apply, ite_eq_left h, mul_one] using
      twoColorSign_mul_of_ne (c i) (c j) (c.valid h)
  · simp only [SimpleGraph.adjMatrix_apply, ite_eq_right h, mul_zero, zero_mul,
      neg_zero]
#print axioms Paper7IntroOddForest.twoColor_adjacency_conjugation

theorem twoColor_charpoly_neg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) :
    (-G.adjMatrix ℤ).charpoly = (G.adjMatrix ℤ).charpoly := by
  let D : Matrix V V ℤ := Matrix.diagonal (fun v => twoColorSign (c v))
  have hD : D * D = 1 := twoColor_diagonal_involutive c
  have hA : D * G.adjMatrix ℤ * D = -G.adjMatrix ℤ :=
    twoColor_adjacency_conjugation G c
  calc
    (-G.adjMatrix ℤ).charpoly = (D * G.adjMatrix ℤ * D).charpoly :=
      congrArg Matrix.charpoly hA.symm
    _ = (D * (G.adjMatrix ℤ * D)).charpoly :=
      congrArg Matrix.charpoly (mul_assoc _ _ _)
    _ = (G.adjMatrix ℤ * D * D).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (G.adjMatrix ℤ * (D * D)).charpoly :=
      congrArg Matrix.charpoly (mul_assoc _ _ _)
    _ = (G.adjMatrix ℤ).charpoly := by rw [hD, mul_one]
#print axioms Paper7IntroOddForest.twoColor_charpoly_neg

theorem matrix_charpoly_eval_neg {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℤ) (x : ℤ) :
    A.charpoly.eval (-x) = (-1 : ℤ) ^ Fintype.card V * (-A).charpoly.eval x := by
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have h : Matrix.scalar V (-x) - A = -(Matrix.scalar V x - -A) := by
    apply Matrix.ext
    intro i j
    simp [sub_eq_add_neg, add_comm]
  rw [h, Matrix.det_neg]
#print axioms Paper7IntroOddForest.matrix_charpoly_eval_neg

theorem twoColor_graphPhi_eval_neg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 2)) (x : ℤ) :
    (graphPhi G).eval (-x) = (-1 : ℤ) ^ Fintype.card V * (graphPhi G).eval x := by
  have h := matrix_charpoly_eval_neg (G.adjMatrix ℤ) x
  rw [twoColor_charpoly_neg G c] at h
  simpa only [Paper7GraphPhi.graphPhi_eq_charpoly] using h
#print axioms Paper7IntroOddForest.twoColor_graphPhi_eval_neg

theorem forest_graphPhi_eval_neg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) (x : ℤ) :
    (graphPhi G).eval (-x) = (-1 : ℤ) ^ Fintype.card V * (graphPhi G).eval x :=
  twoColor_graphPhi_eval_neg G hG.coloringTwo x
#print axioms Paper7IntroOddForest.forest_graphPhi_eval_neg

theorem forest_graphPhi_comp_neg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    (graphPhi G).comp (-X) = C ((-1 : ℤ) ^ Fintype.card V) * graphPhi G := by
  apply Polynomial.funext
  intro x
  simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] using forest_graphPhi_eval_neg G hG x
#print axioms Paper7IntroOddForest.forest_graphPhi_comp_neg

end Paper7IntroOddForest
