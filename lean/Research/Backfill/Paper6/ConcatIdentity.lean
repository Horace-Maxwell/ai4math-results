import Research.Backfill.Paper6.ChallengeV3

/-!
# Paper 6 V3: four-block concatenation

The frozen target `BackfillPaper6.V3.Sec4Concat` contains both the pointwise
concatenation identity and membership in RM(7,14). This file proves both.
For the identity, the last two coordinates have the four values 00, 10, 01, 11.
For membership, rename the two degree-at-most-six polynomials along the first
12 coordinates, multiply them by X_12 and X_13 respectively, and add them.
Renaming cannot increase total degree, so the resulting degree is at most seven.

Frozen contract manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Authoring this source is not a claim of successful compilation or acceptance.
-/

set_option autoImplicit false

namespace Paper6Concat

open BackfillPaper6.V3

/-- The four-block formula is an identity for arbitrary binary functions. -/
theorem cat4_zero_eq_xAB (A B : BFun 12) :
    cat4 0 A B (A + B) = xAB A B := by
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  funext y
  rcases hbit (y 12) with h12 | h12 <;>
    rcases hbit (y 13) with h13 | h13 <;>
      simp [cat4, xAB, h12, h13]

/-- A concrete polynomial for x13 A + x14 B, using zero-based variable indices. -/
noncomputable def concatPolynomial
    (p q : MvPolynomial (Fin 12) (ZMod 2)) :
    MvPolynomial (Fin 14) (ZMod 2) :=
  MvPolynomial.X 12 * MvPolynomial.rename (Fin.castAdd 2) p +
    MvPolynomial.X 13 * MvPolynomial.rename (Fin.castAdd 2) q

/-- Renaming along castAdd implements precisely the frozen lo12 coordinate map. -/
theorem evalFun_concatPolynomial
    (p q : MvPolynomial (Fin 12) (ZMod 2)) :
    evalFun (concatPolynomial p q) = xAB (evalFun p) (evalFun q) := by
  funext y
  simp only [evalFun, concatPolynomial, xAB,
    MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_rename, Function.comp_def]
  rfl

/-- Adding one new variable to each renamed polynomial gives degree at most seven. -/
theorem concatPolynomial_degree_le
    (p q : MvPolynomial (Fin 12) (ZMod 2))
    (hp : p.totalDegree ≤ 6) (hq : q.totalDegree ≤ 6) :
    (concatPolynomial p q).totalDegree ≤ 7 := by
  have hp' : (MvPolynomial.rename (Fin.castAdd 2) p).totalDegree ≤ 6 :=
    (MvPolynomial.totalDegree_rename_le (Fin.castAdd 2) p).trans hp
  have hq' : (MvPolynomial.rename (Fin.castAdd 2) q).totalDegree ≤ 6 :=
    (MvPolynomial.totalDegree_rename_le (Fin.castAdd 2) q).trans hq
  have hleft :
      ((MvPolynomial.X 12 : MvPolynomial (Fin 14) (ZMod 2)) *
        MvPolynomial.rename (Fin.castAdd 2) p).totalDegree ≤ 7 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa only [MvPolynomial.totalDegree_X] using
        (Nat.add_le_add (le_refl 1) hp'))
  have hright :
      ((MvPolynomial.X 13 : MvPolynomial (Fin 14) (ZMod 2)) *
        MvPolynomial.rename (Fin.castAdd 2) q).totalDegree ≤ 7 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa only [MvPolynomial.totalDegree_X] using
        (Nat.add_le_add (le_refl 1) hq'))
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hleft hright)

/-- The constructed function belongs to the actual polynomial-defined code. -/
theorem xAB_mem_RM (A B : BFun 12)
    (hA : A ∈ RM 6 12) (hB : B ∈ RM 6 12) :
    xAB A B ∈ RM 7 14 := by
  rcases hA with ⟨p, hp, hAp⟩
  rcases hB with ⟨q, hq, hBq⟩
  refine ⟨concatPolynomial p q, concatPolynomial_degree_le p q hp hq, ?_⟩
  rw [hAp, hBq]
  exact (evalFun_concatPolynomial p q).symm

/-- Exact frozen statement, including its code-membership conclusion. -/
theorem sec4Concat : BackfillPaper6.V3.Sec4Concat := by
  intro A hA B hB
  exact ⟨cat4_zero_eq_xAB A B, xAB_mem_RM A B hA hB⟩

/-- The final declaration is checked against the unchanged frozen contract. -/
theorem check_Sec4Concat : BackfillPaper6.V3.Sec4Concat := sec4Concat

end Paper6Concat

#print axioms Paper6Concat.cat4_zero_eq_xAB
#print axioms Paper6Concat.evalFun_concatPolynomial
#print axioms Paper6Concat.concatPolynomial_degree_le
#print axioms Paper6Concat.xAB_mem_RM
#print axioms Paper6Concat.sec4Concat
#print axioms Paper6Concat.check_Sec4Concat
#print Paper6Concat.check_Sec4Concat
