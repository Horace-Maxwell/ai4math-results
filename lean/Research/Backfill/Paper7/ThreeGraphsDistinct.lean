import Research.Backfill.Paper7.ChallengeV3

/-! Pairwise non-isomorphism of the three actual frozen sun graphs. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7ThreeGraphsDistinct

open BackfillPaper7.Challenge

theorem card_G13 : Fintype.card (SunV 4 G13) = 13 := by
  decide +kernel

#print axioms Paper7ThreeGraphsDistinct.card_G13

theorem card_G20a : Fintype.card (SunV 4 G20a) = 20 := by
  decide +kernel

#print axioms Paper7ThreeGraphsDistinct.card_G20a

theorem card_G20b : Fintype.card (SunV 4 G20b) = 20 := by
  decide +kernel

#print axioms Paper7ThreeGraphsDistinct.card_G20b

theorem degree_G20a_zero : (sunGraph 4 G20a).degree (Sum.inl 0) = 7 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

#print axioms Paper7ThreeGraphsDistinct.degree_G20a_zero

theorem degree_G20b_le_six : ∀ v : SunV 4 G20b, (sunGraph 4 G20b).degree v ≤ 6 := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

#print axioms Paper7ThreeGraphsDistinct.degree_G20b_le_six

theorem G13_not_iso_G20a : IsEmpty (sunGraph 4 G13 ≃g sunGraph 4 G20a) := by
  refine ⟨fun e => ?_⟩
  have h := Fintype.card_congr e.toEquiv
  rw [card_G13, card_G20a] at h
  omega

#print axioms Paper7ThreeGraphsDistinct.G13_not_iso_G20a

theorem G13_not_iso_G20b : IsEmpty (sunGraph 4 G13 ≃g sunGraph 4 G20b) := by
  refine ⟨fun e => ?_⟩
  have h := Fintype.card_congr e.toEquiv
  rw [card_G13, card_G20b] at h
  omega

#print axioms Paper7ThreeGraphsDistinct.G13_not_iso_G20b

theorem G20a_not_iso_G20b : IsEmpty (sunGraph 4 G20a ≃g sunGraph 4 G20b) := by
  refine ⟨fun e => ?_⟩
  have he : (sunGraph 4 G20b).degree (e (Sum.inl 0)) = 7 :=
    (e.degree_eq (Sum.inl 0)).trans degree_G20a_zero
  have hb := degree_G20b_le_six (e (Sum.inl 0))
  omega

#print axioms Paper7ThreeGraphsDistinct.G20a_not_iso_G20b

theorem check_Theorem2GraphsDistinct :
    BackfillPaper7.Challenge.Theorem2GraphsDistinct := by
  exact ⟨G13_not_iso_G20a, G13_not_iso_G20b, G20a_not_iso_G20b⟩

#print axioms Paper7ThreeGraphsDistinct.check_Theorem2GraphsDistinct

end Paper7ThreeGraphsDistinct
