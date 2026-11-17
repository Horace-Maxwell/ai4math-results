import Research.TaskH.Six.SixEqualityDegreeTen
import Research.TaskH.Six.SixDegreeTenSplitPacking
import Research.TaskH.Six.SixDegreeTenCommonPacking
import Research.TaskH.Six.RegressionSix

/-! Exact frozen k=6 partial target. The original all-k question remains unchanged. -/

set_option autoImplicit false

universe u

namespace TaskH

theorem case_six : Challenge.CaseSix.{u} := by
  intro V _ G hcrit hcount
  classical
  have hc : Challenge.modCycleCount 6 G = 420 :=
    hcount.trans Six.completeSeven_check.2.2
  by_contra hnot
  obtain ⟨v, hv⟩ := Six.equality_exists_degree_ten hcrit hc hnot
  have hs : Six.ShortSixCycles G := Six.equality_shortSixCycles hcrit hc
  have hr : Six.RainbowSixCycles G := Six.equality_rainbowSixCycles hcrit hc
  have hfree := Six.equality_degree_ten_cliqueFree_four hcrit hc hnot v hv
  have hmin := Six.equality_degree_ge_ten hcrit hc hnot
  have hn36 := Six.equality_degree_ten_card_le_thirty_six hcrit hc hnot v hv
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  obtain ⟨F, hA | hB⟩ := Six.degreeTen_actual_neighbor_dichotomy hcrit hs hr hfree v c hv
  · obtain ⟨ε, hε⟩ := hA
    exact Six.degreeTen_split_packing_impossible hr F ε hε hv hmin hn36
  · obtain ⟨r, hr'⟩ := hB
    exact Six.degreeTen_common_packing_impossible hr F r hr' hv hmin hn36

end TaskH

#print axioms TaskH.case_six
#print axioms TaskH.Six.completeSeven_check
