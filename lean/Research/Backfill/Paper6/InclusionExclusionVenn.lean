import Research.Backfill.Paper6.InclusionExclusion

/-!
# Venn-region invariance of the weight of an arbitrary monomial sum

Candidate source only, not compiled or independently reviewed. Its final theorem
has the exact frozen V3.Lem21_venn type. The imported InclusionExclusion candidate
also remains pending compilation and acceptance.

Each union indexed by T is partitioned by the Venn patterns meeting T. Every such
pattern is nonempty, so the frozen hypothesis supplies all required cardinalities.
No hypothesis about the empty Venn pattern or about nonempty families is added.
-/

set_option autoImplicit false

namespace Paper6InclusionExclusionVenn

open Finset
open BackfillPaper6.V3

/-- The set of monomials in which coordinate j occurs. -/
def pattern {m k : ℕ} (S : Fin k → Finset (Fin m)) (j : Fin m) : Finset (Fin k) :=
  Finset.univ.filter fun i => j ∈ S i

/-- Exactly the Venn patterns which contribute to the union indexed by T. -/
def meetingPatterns {k : ℕ} (T : Finset (Fin k)) : Finset (Finset (Fin k)) :=
  Finset.univ.filter fun U => (T ∩ U).Nonempty

theorem mem_pattern {m k : ℕ} (S : Fin k → Finset (Fin m))
    (j : Fin m) (i : Fin k) : i ∈ pattern S j ↔ j ∈ S i := by
  simp only [pattern, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_meetingPatterns {k : ℕ} (T U : Finset (Fin k)) :
    U ∈ meetingPatterns T ↔ (T ∩ U).Nonempty := by
  simp only [meetingPatterns, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_venn_region {m k : ℕ} (S : Fin k → Finset (Fin m))
    (U : Finset (Fin k)) (j : Fin m) :
    j ∈ venn S U ↔ ∀ i, j ∈ S i ↔ i ∈ U := by
  simp only [venn, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Distinct membership patterns always describe disjoint coordinate regions. -/
theorem venn_disjoint {m k : ℕ} (S : Fin k → Finset (Fin m))
    {U V : Finset (Fin k)} (hUV : U ≠ V) : Disjoint (venn S U) (venn S V) := by
  apply Finset.disjoint_left.mpr
  intro j hjU hjV
  apply hUV
  apply Finset.ext
  intro i
  exact ((mem_venn_region S U j).mp hjU i).symm.trans
    ((mem_venn_region S V j).mp hjV i)

/-- A union of monomial supports consists exactly of the regions meeting its index set. -/
theorem union_eq_venn_biUnion {m k : ℕ} (S : Fin k → Finset (Fin m))
    (T : Finset (Fin k)) :
    T.biUnion S = (meetingPatterns T).biUnion (venn S) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hiT, hji⟩ := Finset.mem_biUnion.mp hj
    apply Finset.mem_biUnion.mpr
    refine ⟨pattern S j, ?_, ?_⟩
    · apply (mem_meetingPatterns T (pattern S j)).mpr
      exact ⟨i, Finset.mem_inter.mpr ⟨hiT, (mem_pattern S j i).mpr hji⟩⟩
    · apply (mem_venn_region S (pattern S j) j).mpr
      intro l
      exact (mem_pattern S j l).symm
  · intro hj
    obtain ⟨U, hU, hjU⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, hi⟩ := (mem_meetingPatterns T U).mp hU
    exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_inter.mp hi).1,
      ((mem_venn_region S U j).mp hjU i).mpr (Finset.mem_inter.mp hi).2⟩

/-- The disjoint Venn partition gives the union cardinality, also when T is empty. -/
theorem union_card_as_venn_sum {m k : ℕ} (S : Fin k → Finset (Fin m))
    (T : Finset (Fin k)) :
    (T.biUnion S).card = ∑ U ∈ meetingPatterns T, (venn S U).card := by
  rw [union_eq_venn_biUnion S T]
  apply Finset.card_biUnion
  intro U _hU V _hV hUV
  exact venn_disjoint S hUV

/-- Nonempty-region data suffice for every union; the empty region never contributes. -/
theorem union_card_eq {m k : ℕ} (S S' : Fin k → Finset (Fin m))
    (h : ∀ U : Finset (Fin k), U.Nonempty → (venn S U).card = (venn S' U).card)
    (T : Finset (Fin k)) : (T.biUnion S).card = (T.biUnion S').card := by
  rw [union_card_as_venn_sum S T, union_card_as_venn_sum S' T]
  apply Finset.sum_congr rfl
  intro U hU
  apply h U
  obtain ⟨i, hi⟩ := (mem_meetingPatterns T U).mp hU
  exact ⟨i, (Finset.mem_inter.mp hi).2⟩

/-- The exact frozen Venn-invariance statement, without an empty-region hypothesis. -/
theorem check_Lem21_venn : BackfillPaper6.V3.Lem21_venn := by
  classical
  intro m k S S' h
  have hw :
      (hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S i, x j) : ℤ) =
        (hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S' i, x j) : ℤ) := by
    rw [Paper6InclusionExclusion.check_Lem21 m k S,
      Paper6InclusionExclusion.check_Lem21 m k S']
    apply Finset.sum_congr rfl
    intro T _hT
    rw [union_card_eq S S' h T]
  exact_mod_cast hw

end Paper6InclusionExclusionVenn

#print axioms Paper6InclusionExclusionVenn.mem_pattern
#print axioms Paper6InclusionExclusionVenn.mem_meetingPatterns
#print axioms Paper6InclusionExclusionVenn.mem_venn_region
#print axioms Paper6InclusionExclusionVenn.venn_disjoint
#print axioms Paper6InclusionExclusionVenn.union_eq_venn_biUnion
#print axioms Paper6InclusionExclusionVenn.union_card_as_venn_sum
#print axioms Paper6InclusionExclusionVenn.union_card_eq
#print axioms Paper6InclusionExclusionVenn.check_Lem21_venn
