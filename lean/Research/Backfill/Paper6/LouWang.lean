import Research.Backfill.Paper6.ConcatIdentity

/-!
# The literal Lou–Wang construction belongs to RM(7,14)

Complete source candidates for the frozen LWConstrInRM and LWConj2_gives targets.
This module has not been compiled or independently reviewed.

The four arbitrary six-term index sequences are kept as indexed products; repeated
indices are allowed. The two arbitrary binary constants are represented by the
correction a1*X12 + (a1+a2)*X12*X13, of degree at most two. Adding this to the
accepted concatPolynomial gives exactly the frozen four-block function.

The final set inclusion uses that same function as its actual codeword witness.
No assumption of LWConj2_m6, or contradiction from its refutation, is used.
-/

set_option autoImplicit false

namespace Paper6LouWang

open Finset
open BackfillPaper6.V3

/-- Six indexed factors, with no distinctness condition on the indices. -/
noncomputable def sequencePolynomial (i : Fin 6 → Fin 12) :
    MvPolynomial (Fin 12) (ZMod 2) := ∏ j, MvPolynomial.X (i j)

/-- The fixed monomial on the first six coordinates. -/
noncomputable def basePolynomial : MvPolynomial (Fin 12) (ZMod 2) :=
  ∏ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 12)), MvPolynomial.X j

/-- One of the two three-monomial functions in the frozen construction. -/
noncomputable def triplePolynomial (i j : Fin 6 → Fin 12) :
    MvPolynomial (Fin 12) (ZMod 2) :=
  basePolynomial + sequencePolynomial i + sequencePolynomial j

/-- The constants in blocks 10 and 11 are supplied by a quadratic in the new coordinates. -/
noncomputable def correctionPolynomial (a1 a2 : ZMod 2) :
    MvPolynomial (Fin 14) (ZMod 2) :=
  MvPolynomial.C a1 * MvPolynomial.X 12 +
    MvPolynomial.C (a1 + a2) * MvPolynomial.X 12 * MvPolynomial.X 13

/-- A concrete polynomial whose evaluation is exactly the frozen lwG. -/
noncomputable def lwPolynomial
    (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) :
    MvPolynomial (Fin 14) (ZMod 2) :=
  Paper6Concat.concatPolynomial (triplePolynomial i1 i2) (triplePolynomial i3 i4) +
    correctionPolynomial a1 a2

theorem sequencePolynomial_degree_le (i : Fin 6 → Fin 12) :
    (sequencePolynomial i).totalDegree ≤ 6 := by
  simpa [sequencePolynomial] using
    (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin 6))
      (fun j => (MvPolynomial.X (i j) : MvPolynomial (Fin 12) (ZMod 2))))

theorem basePolynomial_degree_le : basePolynomial.totalDegree ≤ 6 := by
  calc
    basePolynomial.totalDegree ≤
        ∑ _j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 12)), (1 : ℕ) := by
      simpa only [basePolynomial, MvPolynomial.totalDegree_X] using
        (MvPolynomial.totalDegree_finsetProd
          ({0, 1, 2, 3, 4, 5} : Finset (Fin 12))
          (fun j => (MvPolynomial.X j : MvPolynomial (Fin 12) (ZMod 2))))
    _ = 6 := by decide

theorem triplePolynomial_degree_le (i j : Fin 6 → Fin 12) :
    (triplePolynomial i j).totalDegree ≤ 6 := by
  unfold triplePolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le
      ((MvPolynomial.totalDegree_add _ _).trans
        (max_le basePolynomial_degree_le (sequencePolynomial_degree_le i)))
      (sequencePolynomial_degree_le j))

theorem evalFun_triplePolynomial (i j : Fin 6 → Fin 12) :
    evalFun (triplePolynomial i j) = x16 + prodSeq i + prodSeq j := by
  funext x
  simp only [evalFun, triplePolynomial, basePolynomial, sequencePolynomial,
    x16, prodSeq, Pi.add_apply, MvPolynomial.eval_add,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]

/-- The four-block scalar identity has only six binary inputs. -/
theorem binary_concat_formula (A B a1 a2 b c : ZMod 2) :
    (if b = 0 then (if c = 0 then 0 else B)
      else (if c = 0 then A + a1 else A + B + a2)) =
      b * A + c * B + (a1 * b + (a1 + a2) * b * c) := by
  revert A B a1 a2 b c
  decide

theorem evalFun_lwPolynomial
    (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) :
    evalFun (lwPolynomial i1 i2 i3 i4 a1 a2) = lwG i1 i2 i3 i4 a1 a2 := by
  funext y
  change MvPolynomial.eval y
    (Paper6Concat.concatPolynomial (triplePolynomial i1 i2) (triplePolynomial i3 i4) +
      correctionPolynomial a1 a2) = _
  rw [MvPolynomial.eval_add]
  change evalFun
    (Paper6Concat.concatPolynomial (triplePolynomial i1 i2) (triplePolynomial i3 i4)) y +
      MvPolynomial.eval y (correctionPolynomial a1 a2) = _
  rw [Paper6Concat.evalFun_concatPolynomial,
    evalFun_triplePolynomial, evalFun_triplePolynomial]
  simp only [correctionPolynomial, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact (binary_concat_formula
    ((x16 + prodSeq i1 + prodSeq i2) (lo12 y))
    ((x16 + prodSeq i3 + prodSeq i4) (lo12 y)) a1 a2 (y 12) (y 13)).symm

theorem correctionPolynomial_degree_le (a1 a2 : ZMod 2) :
    (correctionPolynomial a1 a2).totalDegree ≤ 2 := by
  have hlinear (a : ZMod 2) :
      ((MvPolynomial.C a : MvPolynomial (Fin 14) (ZMod 2)) *
        MvPolynomial.X 12).totalDegree ≤ 1 := by
    simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
      (MvPolynomial.totalDegree_mul
        (MvPolynomial.C a : MvPolynomial (Fin 14) (ZMod 2)) (MvPolynomial.X 12))
  have hquadratic :
      ((MvPolynomial.C (a1 + a2) : MvPolynomial (Fin 14) (ZMod 2)) *
        MvPolynomial.X 12 * MvPolynomial.X 13).totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa only [MvPolynomial.totalDegree_X] using
        (Nat.add_le_add (hlinear (a1 + a2)) (le_refl 1)))
  unfold correctionPolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((hlinear a1).trans (by decide)) hquadratic)

theorem lwPolynomial_degree_le
    (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) :
    (lwPolynomial i1 i2 i3 i4 a1 a2).totalDegree ≤ 7 := by
  unfold lwPolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le
      (Paper6Concat.concatPolynomial_degree_le _ _
        (triplePolynomial_degree_le i1 i2) (triplePolynomial_degree_le i3 i4))
      ((correctionPolynomial_degree_le a1 a2).trans (by decide)))

/-- Every parameter choice in the exact frozen construction has a genuine degree-seven witness. -/
theorem check_LWConstrInRM : BackfillPaper6.V3.LWConstrInRM := by
  intro i1 i2 i3 i4 a1 a2
  exact ⟨lwPolynomial i1 i2 i3 i4 a1 a2,
    lwPolynomial_degree_le i1 i2 i3 i4 a1 a2,
    (evalFun_lwPolynomial i1 i2 i3 i4 a1 a2).symm⟩

/-- These five numbers occur at indices 1, 3, 5, 7, 17 in the indicated arithmetic family. -/
theorem conjecturedFamily_indices :
    ∀ w ∈ ({322, 326, 330, 334, 354} : Finset ℕ),
      ∃ i < 2 ^ 6, w = 2 ^ 8 + 2 ^ 6 + 2 * i := by
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩
  · exact ⟨17, by decide, by decide⟩

/-- Exact frozen arithmetic content and actual spectrum inclusion, with no conjecture premise. -/
theorem check_LWConj2_gives : BackfillPaper6.V3.LWConj2_gives := by
  constructor
  · exact conjecturedFamily_indices
  · intro w hw
    rcases hw with ⟨i1, i2, i3, i4, a1, a2, hweight⟩
    exact ⟨lwG i1 i2 i3 i4 a1 a2, check_LWConstrInRM i1 i2 i3 i4 a1 a2, hweight⟩

end Paper6LouWang

#print axioms Paper6LouWang.sequencePolynomial
#print axioms Paper6LouWang.basePolynomial
#print axioms Paper6LouWang.triplePolynomial
#print axioms Paper6LouWang.correctionPolynomial
#print axioms Paper6LouWang.lwPolynomial
#print axioms Paper6LouWang.sequencePolynomial_degree_le
#print axioms Paper6LouWang.basePolynomial_degree_le
#print axioms Paper6LouWang.triplePolynomial_degree_le
#print axioms Paper6LouWang.evalFun_triplePolynomial
#print axioms Paper6LouWang.binary_concat_formula
#print axioms Paper6LouWang.evalFun_lwPolynomial
#print axioms Paper6LouWang.correctionPolynomial_degree_le
#print axioms Paper6LouWang.lwPolynomial_degree_le
#print axioms Paper6LouWang.check_LWConstrInRM
#print axioms Paper6LouWang.conjecturedFamily_indices
#print axioms Paper6LouWang.check_LWConj2_gives
