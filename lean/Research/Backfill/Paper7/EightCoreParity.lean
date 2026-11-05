import Research.Backfill.Paper7.EightCorePolynomial
import Research.Backfill.Paper7.EightBinaryProfiles

/-! Source-only mod-two core certificate. This is a fixed eight-by-eight
determinant identity and contains no parameter search or assumed CRT test. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped Matrix BigOperators CharTwo

theorem cycleEight_adj_iff :
    ∀ i k : Fin 8, (SimpleGraph.cycleGraph 8).Adj i k ↔
      i.val + 1 = k.val ∨ k.val + 1 = i.val ∨
        (i = 0 ∧ k = 7) ∨ (i = 7 ∧ k = 0) := by
  decide +kernel
#print axioms Paper7EightCycle.cycleEight_adj_iff

theorem cycleAdjZ_eight_matrix :
    cycleAdjZ 8 =
      !![0,1,0,0,0,0,0,1;
         1,0,1,0,0,0,0,0;
         0,1,0,1,0,0,0,0;
         0,0,1,0,1,0,0,0;
         0,0,0,1,0,1,0,0;
         0,0,0,0,1,0,1,0;
         0,0,0,0,0,1,0,1;
         1,0,0,0,0,0,1,0] := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, cycleEight_adj_iff]
#print axioms Paper7EightCycle.cycleAdjZ_eight_matrix

open scoped Classical

def coreModTwo : Polynomial ℤ →+* Polynomial (ZMod 2) :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod 2))
#print axioms Paper7EightCycle.coreModTwo

def binaryDiagonal (j i : Fin 8) : Polynomial (ZMod 2) :=
  X^2+if i = 0 ∨ i = j then 1 else 0
#print axioms Paper7EightCycle.binaryDiagonal

def binaryCore (j : Fin 8) : Matrix (Fin 8) (Fin 8) (Polynomial (ZMod 2)) :=
  !![binaryDiagonal j 0,X,0,0,0,0,0,X;
     X,binaryDiagonal j 1,X,0,0,0,0,0;
     0,X,binaryDiagonal j 2,X,0,0,0,0;
     0,0,X,binaryDiagonal j 3,X,0,0,0;
     0,0,0,X,binaryDiagonal j 4,X,0,0;
     0,0,0,0,X,binaryDiagonal j 5,X,0;
     0,0,0,0,0,X,binaryDiagonal j 6,X;
     X,0,0,0,0,0,X,binaryDiagonal j 7]
#print axioms Paper7EightCycle.binaryCore

theorem remaining_core_mod_two (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    coreModTwo (coreF p) = X^16+X^12 := by
  rw [eight_remaining_coreF p hp hn hG]
  norm_num [coreModTwo]
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.remaining_core_mod_two

theorem core_matrix_mod_two (p : Fin 8 → ℕ) (j : Fin 8)
    (hpar : ∀ i : Fin 8, (p i : ZMod 2) = if i = 0 ∨ i = j then 1 else 0) :
    coreModTwo.mapMatrix (coreMatrix p) = binaryCore j := by
  have hpoly (i : Fin 8) : (p i : Polynomial (ZMod 2)) =
      if i = 0 ∨ i = j then 1 else 0 := by
    have hc := congrArg (fun z : ZMod 2 => (C z : Polynomial (ZMod 2))) (hpar i)
    rw [Polynomial.C_eq_natCast] at hc
    by_cases hi : i = 0 ∨ i = j
    · rw [ite_eq_left hi, Polynomial.C_1] at hc
      rw [ite_eq_left hi]
      exact hc
    · rw [ite_eq_right hi, Polynomial.C_0] at hc
      rw [ite_eq_right hi]
      exact hc
  funext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [RingHom.mapMatrix_apply,coreModTwo,coreMatrix,binaryCore,binaryDiagonal,
      cycleAdjZ_eight_matrix,hpoly]
#print axioms Paper7EightCycle.core_matrix_mod_two

theorem binary_core_det (j : Fin 8) :
    (binaryCore j).det =
      if j = 0 then X^16+X^14 else
      if j = 1 ∨ j = 7 then X^16+X^12+X^10+X^6 else
      if j = 2 ∨ j = 6 then X^16+X^12+X^8 else
      if j = 3 ∨ j = 5 then X^16+X^12+X^6 else X^16+X^12 := by
  have hm : binaryCore j = binaryCycleProfile j (X : Polynomial (ZMod 2)) := rfl
  rw [hm]
  exact binary_cycle_profile_det j X
#print axioms Paper7EightCycle.binary_core_det

theorem binary_core_forces_opposite (j : Fin 8) (hj : j ≠ 0)
    (hdet : (binaryCore j).det = X^16+X^12) : j = 4 := by
  rw [binary_core_det] at hdet
  fin_cases j <;> norm_num at *
  all_goals
    have hc := congrArg (fun f : Polynomial (ZMod 2) => f.coeff 6) hdet
    norm_num at hc
#print axioms Paper7EightCycle.binary_core_forces_opposite

theorem eight_integral_two_odd_opposite (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0)))
    (j : Fin 8) (hj : j ≠ 0)
    (hpar : ∀ i : Fin 8, (p i : ZMod 2) = if i = 0 ∨ i = j then 1 else 0) : j = 4 := by
  apply binary_core_forces_opposite j hj
  have he := coreModTwo.map_det (coreMatrix p)
  have hcore : coreF p = (coreMatrix p).det :=
    (coreF_apply_eq p).trans (finCoreDet_eq_det 8 (coreMatrix p))
  rw [← hcore,core_matrix_mod_two p j hpar] at he
  exact he.symm.trans (remaining_core_mod_two p hp hn hG)
#print axioms Paper7EightCycle.eight_integral_two_odd_opposite

end Paper7EightCycle
