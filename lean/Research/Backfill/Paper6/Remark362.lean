import Research.Backfill.Paper6.RemarkWitnesses

/-!
# An analytic five-monomial candidate of weight 362

The two seven-variable blocks are A = {0,...,6} and B = {7,...,13}.
Let R = {7,...,11}.  The five supports are A, B, R∪{0,1}, R∪{2,3},
and R∪{4,5}.  Their literal masks are recorded below.

This data was derived algebraically, not obtained by running a search.
The complete hand derivation is in analytic-362-candidate.md.  All concrete
claims below remain actual kernel obligations: no execution or acceptance
is claimed by writing this candidate source.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6RemarkWitnesses

open BackfillPaper6.V3
open Paper6S0Witnesses

def row_362 : ℕ × List ℕ := (362, [127, 16256, 3971, 3980, 4016])

set_option maxHeartbeats 200000 in
theorem row_362_valid : RowData5 row_362 := by
  decide +kernel

theorem row_362_distinct : row_362.2.Nodup := by
  decide +kernel

theorem row_362_degrees : ∀ s ∈ row_362.2, RM714.degNat s = 7 := by
  decide +kernel

/-- The actual ANF polynomial, without an existentially chosen replacement. -/
noncomputable def polynomial_362 : MvPolynomial (Fin 14) (ZMod 2) :=
  polyOf (row_362.2.map RM714.maskSet)

/-- Both frozen bounds and the actual Hamming weight of this specific polynomial. -/
theorem polynomial_362_spec :
    polynomial_362.support.card ≤ 5 ∧ polynomial_362.totalDegree ≤ 7 ∧
      hammingNorm (evalFun polynomial_362) = 362 := by
  have h := row_362_valid
  change (polyOf (row_362.2.map RM714.maskSet)).support.card ≤ 5 ∧
    (polyOf (row_362.2.map RM714.maskSet)).totalDegree ≤ 7 ∧
      hammingNorm (evalFun (polyOf (row_362.2.map RM714.maskSet))) = 362
  refine ⟨?_, ?_, ?_⟩
  · exact (Paper6ThmA.polyOf_support_card_le _).trans
      (by simpa only [List.length_map] using h.2.2.1)
  · apply Paper6ThmA.polyOf_degree_le
    intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
    rw [RM714.card_maskSet]
    exact h.2.1 s hs
  · have heq := charCount_zero row_362.2
    have hcert := h.2.2.2
    have hw :
        (hammingNorm (evalFun (polyOf (row_362.2.map RM714.maskSet))) : ℤ) =
          (row_362.1 : ℤ) := by linarith
    have hwNat : hammingNorm (evalFun (polyOf (row_362.2.map RM714.maskSet))) =
        row_362.1 := by exact_mod_cast hw
    exact hwNat

theorem weight_362 : 362 ∈ weightsLe5 :=
  ⟨polynomial_362, polynomial_362_spec⟩

end Paper6RemarkWitnesses

#print axioms Paper6RemarkWitnesses.row_362
#print axioms Paper6RemarkWitnesses.row_362_valid
#print axioms Paper6RemarkWitnesses.row_362_distinct
#print axioms Paper6RemarkWitnesses.row_362_degrees
#print axioms Paper6RemarkWitnesses.polynomial_362
#print axioms Paper6RemarkWitnesses.polynomial_362_spec
#print axioms Paper6RemarkWitnesses.weight_362
