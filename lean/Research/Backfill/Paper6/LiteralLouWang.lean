import Research.Backfill.Paper6.LiteralVenn
import Research.Backfill.Paper6.LiteralConstruction

/-!
# Exact frozen ThmC_literal — known Lou–Wang refutation

Complete source candidate only. The imported finite Venn certificates and all
semantic bridges remain uncompiled until Root verifies them. No low-weight table
is assumed: it is a conclusion of the complete bounded 3/4-set certificates.
All four six-index sequences (including repetitions) and both constants are kept.
-/

set_option autoImplicit false

namespace Paper6LiteralLouWang

open BackfillPaper6.V3

theorem triple_low_weight (i j : Fin 6 → Fin 12)
    (hsmall : hammingNorm (tripleFunction i j) ≤ 161) :
    hammingNorm (tripleFunction i j) ∈ smallWeights := by
  rw [triple_as_sum] at hsmall ⊢
  refine low_weight3 _ ?_ hsmall
  intro a
  fin_cases a
  · change ({0, 1, 2, 3, 4, 5} : Finset (Fin 12)).card ≤ 6
    decide
  · exact sequenceSet_card i
  · exact sequenceSet_card j

theorem triples_sum_low_weight (i1 i2 i3 i4 : Fin 6 → Fin 12)
    (hsmall : hammingNorm (tripleFunction i1 i2 + tripleFunction i3 i4) ≤ 161) :
    hammingNorm (tripleFunction i1 i2 + tripleFunction i3 i4) ∈ smallWeights := by
  rw [triples_sum_as_four] at hsmall ⊢
  refine low_weight4 _ ?_ hsmall
  intro a
  fin_cases a
  · exact sequenceSet_card i1
  · exact sequenceSet_card i2
  · exact sequenceSet_card i3
  · exact sequenceSet_card i4

/-- Exclusion for the actual frozen function, not for an abstract weight triple. -/
theorem literal_ne_322 (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) :
    hammingNorm (lwG i1 i2 i3 i4 a1 a2) ≠ 322 := by
  intro hbad
  let A := tripleFunction i1 i2
  let B := tripleFunction i3 i4
  have ht := (literal_weight i1 i2 i3 i4 a1 a2).symm.trans hbad
  change hammingNorm (A + fun _ => a1) + hammingNorm B +
    hammingNorm (A + B + fun _ => a2) = 322 at ht
  have htri := triangle_three A B
  have hAbound : hammingNorm A ≤ 4096 := by
    simpa using Paper6Parity.hammingNorm_le_points 12 A
  have hCbound : hammingNorm (A + B) ≤ 4096 := by
    simpa using Paper6Parity.hammingNorm_le_points 12 (A + B)
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hbinary a1 with rfl | rfl
  · rcases hbinary a2 with rfl | rfl
    · change hammingNorm (A + 0) + hammingNorm B + hammingNorm (A + B + 0) = 322 at ht
      simp only [add_zero] at ht
      have hsmallA : hammingNorm A ≤ 161 := by omega
      have hsmallB : hammingNorm B ≤ 161 := by omega
      have hsmallC : hammingNorm (A + B) ≤ 161 := by omega
      have hA := triple_low_weight i1 i2 hsmallA
      have hB := triple_low_weight i3 i4 hsmallB
      have hC := triples_sum_low_weight i1 i2 i3 i4 hsmallC
      exact no_322_triple _ hA _ hB _ hC ht
    · change hammingNorm (A + 0) + hammingNorm B + hammingNorm (A + B + 1) = 322 at ht
      rw [add_zero, Paper6Parity.hammingNorm_add_one] at ht
      norm_num at ht
      omega
  · rcases hbinary a2 with rfl | rfl
    · change hammingNorm (A + 1) + hammingNorm B + hammingNorm (A + B + 0) = 322 at ht
      rw [add_zero, Paper6Parity.hammingNorm_add_one] at ht
      norm_num at ht
      omega
    · change hammingNorm (A + 1) + hammingNorm B + hammingNorm (A + B + 1) = 322 at ht
      have hlower := triple_complement_lower i1 i2
      change 512 ≤ hammingNorm (A + 1) at hlower
      omega

theorem literal_not_mem : 322 ∉ lwS := by
  rintro ⟨i1, i2, i3, i4, a1, a2, hweight⟩
  exact literal_ne_322 i1 i2 i3 i4 a1 a2 hweight

/-- Exact complete frozen target; this known result carries no novelty claim. -/
theorem check_ThmC_literal : BackfillPaper6.V3.ThmC_literal := by
  refine ⟨?_, literal_not_mem⟩
  intro hconjecture
  apply literal_not_mem
  simpa using hconjecture.1 1 (by decide)

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.triple_low_weight
#print axioms Paper6LiteralLouWang.triples_sum_low_weight
#print axioms Paper6LiteralLouWang.literal_ne_322
#print axioms Paper6LiteralLouWang.literal_not_mem
#print axioms Paper6LiteralLouWang.check_ThmC_literal
