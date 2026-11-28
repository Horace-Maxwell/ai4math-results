import Research.TaskV.Stanley.CSFBridge
import Research.TaskV.Stanley.AnchorLeaves
import Research.TaskV.Stanley.StarProfiles

namespace StanleyContinuation
open Finset
noncomputable section

/-- The (1,n−1) connected bipartition counts each degree-one vertex once, including at n=2. -/
theorem leafCount_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.IsTree) (hH : H.IsTree) (hn : 2 ≤ n) (same : SameCSF G H) :
    (univ \ core G).card = (univ \ core H).card := by
  obtain rfl := sameOrder_of_sameCSF same
  rw [← singleton_count_eq_leaf_count G hG hn, ← singleton_count_eq_leaf_count H hH hn]
  exact sameConnected_of_sameCSF hG hH same 2 (binarySizes n 1)

/-- For a proper tree the ordinary coloring coefficients recover the entire multiset
of the core weights, against an unrestricted competing tree. -/
theorem coreWeights_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.IsTree) (hH : H.IsTree) (hn : 2 ≤ n)
    (proper : ∀ v ∈ core G, 2 ≤ coreWeight G v) (same : SameCSF G H) :
    ∃ e : ↥(core G) ≃ ↥(core H), ∀ v : ↥(core G), coreWeight H (e v) = coreWeight G v := by
  classical
  have eq := sameConnected_of_sameCSF hG hH same
  have card := same_core_card hG hH (sameOrder_of_sameCSF same) hn eq
  by_cases cg : (core G).Nonempty
  · have ch := card_pos.mp (card ▸ card_pos.mpr cg : 0 < (core H).card)
    exact weightPreservingCoreEquiv hG.connected hH.connected eq cg ch card proper
  · have ec : Fintype.card ↥(core G) = Fintype.card ↥(core H) := by
      simpa only [Fintype.card_coe] using card
    obtain ⟨e⟩ := Fintype.card_eq.mp ec
    exact ⟨e, fun v => (cg ⟨v.val,v.property⟩).elim⟩

end
end StanleyContinuation
