import Research.Backfill.Paper8.Proof.Rows.Members
import Research.Backfill.Paper8.Proof.Rows.CountBare

/-!
# Paper 8, rows: Lemma 4.2 (leaf row) and Lemma 4.3 (bare row)

Assembled from the existence of members and (L), (Z) (`Research.Backfill.Paper8.Proof.Rows.Members`), the formulas (4.1),
(4.2) (`Research.Backfill.Paper8.Proof.Rows.GFormula`) and the counts (`Research.Backfill.Paper8.Proof.Rows.Count`, `Research.Backfill.Paper8.Proof.Rows.CountBare`). Hypotheses:
`StdLeafSums` and Lemma 3.3(a), (b), (e).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Rows

/-- **Lemma 4.2** (leaf row). -/
theorem lemma_4_2 (hStd : StdLeafSums) (h3a : Lemma_3_3_a) (h3b : Lemma_3_3_b)
    (h3e : Lemma_3_3_e) : Lemma_4_2 := by
  intro k a hk hbs β hβ hβ1 L
  refine ⟨fun ε hε Λ hΛ => exists_leafRowMember a hStd β ε hε Λ hΛ,
    fun ε Λ s hs => ?_, fun mem hmem f hf hne => ?_⟩
  · obtain ⟨hL, hZ⟩ := leafRow_condL_condZ a hStd hk hbs β hβ1 ε Λ s hs
    exact ⟨hL, hZ, fun θ hθ => Gs_leaf a β hβ hβ1 ε Λ s hs θ hθ,
      fun f hf hev => leaf_not_failsAtOrbit a β hβ hβ1 h3a hk ε Λ s hs f hf hev⟩
  · exact ⟨fun _ => ⟨fun ε hε => leaf_count_eps a β hβ hβ1 h3b h3e hk mem hmem f hf hne ε hε,
      leaf_count_total a β hβ hβ1 h3b h3e hk mem hmem f hf hne⟩,
      fun hdeg => leaf_count_irr a β hβ hβ1 h3b h3e hk mem hmem f hf hne hdeg⟩

/-- **Lemma 4.3** (bare row). -/
theorem lemma_4_3 (hStd : StdLeafSums) (h3a : Lemma_3_3_a) (h3b : Lemma_3_3_b)
    (h3e : Lemma_3_3_e) : Lemma_4_3 := by
  intro k a hk hbs h0 k0
  refine ⟨fun ε hε mm hmm => exists_bareRowMember a hStd ε hε mm hmm,
    fun ε mm s hs => ?_, fun mem hmem f hf => ?_⟩
  · obtain ⟨hL, hZ⟩ := bareRow_condL_condZ a hStd hk hbs ε mm s hs
    exact ⟨hL, hZ, fun θ hθ => Gs_bare a h0 ε mm s hs θ hθ⟩
  · exact ⟨fun hev => bare_count_even a h0 h3a h3e hk mem hmem f hf hev,
      fun hne _ => bare_count_int a h0 h3b h3e hk mem hmem f hf hne,
      fun hne hdeg => bare_count_irr a h0 h3b h3e hk mem hmem f hf hne hdeg⟩

end P8Rows
