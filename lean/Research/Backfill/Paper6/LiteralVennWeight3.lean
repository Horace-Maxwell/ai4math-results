import Research.Backfill.Paper6.LiteralVennFinite3

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

set_option maxHeartbeats 400000 in
theorem actual_venn_weight3 (S : Fin 3 → Finset (Fin 12)) :
    (hammingNorm (fun x : Pt 12 => ∑ i : Fin 3, ∏ j ∈ S i, x j) : ℤ) = vennWeight3 ((venn S ({0} : Finset (Fin 3))).card) ((venn S ({1} : Finset (Fin 3))).card) ((venn S ({0, 1} : Finset (Fin 3))).card) ((venn S ({2} : Finset (Fin 3))).card) ((venn S ({0, 2} : Finset (Fin 3))).card) ((venn S ({1, 2} : Finset (Fin 3))).card) ((venn S ({0, 1, 2} : Finset (Fin 3))).card) := by
  calc
    (hammingNorm (fun x : Pt 12 => ∑ i : Fin 3, ∏ j ∈ S i, x j) : ℤ) =
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun T => T.Nonempty),
          (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (12 - (T.biUnion S).card) :=
      Paper6InclusionExclusion.check_Lem21 12 3 S
    _ = ∑ T ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun T => T.Nonempty),
          (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^
            (12 - ∑ U ∈ meetingPatterns T, (venn S U).card) := by
      apply Finset.sum_congr rfl
      intro T _hT
      exact congrArg
        (fun n : ℕ => (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (12 - n))
        (union_card_as_venn_sum S T)
    _ = _ := Paper6LiteralVennFinite.formula3 (fun U => (venn S U).card)

#print axioms Paper6LiteralLouWang.actual_venn_weight3

end Paper6LiteralLouWang
