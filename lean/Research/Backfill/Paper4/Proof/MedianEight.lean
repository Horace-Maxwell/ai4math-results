import Research.Backfill.Paper4.Proof.MedianEightRepFacts
import Research.Backfill.Paper4.Proof.MedianEightParent00
import Research.Backfill.Paper4.Proof.MedianEightParent01
import Research.Backfill.Paper4.Proof.MedianEightParent02
import Research.Backfill.Paper4.Proof.MedianEightParent03
import Research.Backfill.Paper4.Proof.MedianEightParent04
import Research.Backfill.Paper4.Proof.MedianEightParent05
import Research.Backfill.Paper4.Proof.MedianEightParent06
import Research.Backfill.Paper4.Proof.MedianEightParent07
import Research.Backfill.Paper4.Proof.MedianEightParent08
import Research.Backfill.Paper4.Proof.MedianEightParent09
import Research.Backfill.Paper4.Proof.MedianEightParent10
import Research.Backfill.Paper4.Proof.MedianEightParent11
import Research.Backfill.Paper4.Proof.MedianEightParent12
import Research.Backfill.Paper4.Proof.MedianEightParent13
import Research.Backfill.Paper4.Proof.MedianEightParent14
import Research.Backfill.Paper4.Proof.MedianEightParent15
import Research.Backfill.Paper4.Proof.MedianEightParent16
import Research.Backfill.Paper4.Proof.MedianEightParent17
import Research.Backfill.Paper4.Proof.MedianEightParent18
import Research.Backfill.Paper4.Proof.MedianEightParent19
import Research.Backfill.Paper4.Proof.MedianEightParent20
import Research.Backfill.Paper4.Proof.MedianEightParent21
import Research.Backfill.Paper4.Proof.MedianEightParent22
import Research.Backfill.Paper4.Proof.MedianEightParent23
import Research.Backfill.Paper4.Proof.MedianEightParent24
import Research.Backfill.Paper4.Proof.MedianEightParent25
import Research.Backfill.Paper4.Proof.MedianEightParent26
import Research.Backfill.Paper4.Proof.MedianEightParent27
import Research.Backfill.Paper4.Proof.MedianEightParent28
import Research.Backfill.Paper4.Proof.MedianEightParent29
import Research.Backfill.Paper4.Proof.MedianEightParent30
import Research.Backfill.Paper4.Proof.MedianEightParent31
import Research.Backfill.Paper4.Proof.MedianEightParent32
import Research.Backfill.Paper4.Proof.MedianEightParent33
import Research.Backfill.Paper4.Proof.MedianEightParent34
import Research.Backfill.Paper4.Proof.MedianEightParent35
import Research.Backfill.Paper4.Proof.MedianEightParent36
import Research.Backfill.Paper4.Proof.MedianEightParent37
import Research.Backfill.Paper4.Proof.MedianEightParent38
import Research.Backfill.Paper4.Proof.MedianEightParent39
import Research.Backfill.Paper4.Proof.MedianEightParent40
import Research.Backfill.Paper4.Proof.MedianEightParent41
import Research.Backfill.Paper4.Proof.MedianEightParent42
import Research.Backfill.Paper4.Proof.MedianEightParent43
import Research.Backfill.Paper4.Proof.MedianEightParent44
import Research.Backfill.Paper4.Proof.MedianEightParent45
import Research.Backfill.Paper4.Proof.MedianEightParent46
import Research.Backfill.Paper4.Proof.MedianEightParent47
import Research.Backfill.Paper4.Proof.MedianEightParent48
import Research.Backfill.Paper4.Proof.MedianEightParent49
import Research.Backfill.Paper4.Proof.MedianEightParent50
import Research.Backfill.Paper4.Proof.MedianEightParent51
import Research.Backfill.Paper4.Proof.MedianEightParent52
import Research.Backfill.Paper4.Proof.MedianEightParent53
import Research.Backfill.Paper4.Proof.MedianEightParent54
import Research.Backfill.Paper4.Proof.MedianEightParent55
import Research.Backfill.Paper4.Proof.MedianEightParent56
import Research.Backfill.Paper4.Proof.MedianEightParent57
import Research.Backfill.Paper4.Proof.MedianEightParent58
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationLayers
import Research.Backfill.Paper4.Proof.MedianMetricTransport
import Research.Backfill.Paper4.Proof.ReductionBasics
import Research.Backfill.Paper4.Proof.Readings
import Research.Backfill.Paper4.Proof.ConcreteRemarks

/-!
# Median graphs with eight vertices: coverage by the 69 representatives, and the uniqueness
statements of Theorems A and B (`TheoremA_unique`, `TheoremB_unique`)

(Written by Claude, 2026-09-28, while Codex was out of quota.) A median graph with eight
vertices has a vertex whose removal leaves a connected graph (Mathlib's
`exists_connected_induce_compl_singleton_of_finite_nontrivial`), triangle-free because the graph
is (Codex's `check_Sec4_median_triangleFree`), which is isomorphic to one of the 59 representatives
(`covers_through_seven`); so the graph is `augment (reps 7 i) S` for a nonempty independent `S`,
up to isomorphism. For every such pair the parent blocks show: not median, or isomorphic to one
of the 69 representatives `L8 j`. Each `L8 j` has (Q3′) and (Q4), or is `G1` or `G2`.
-/

set_option autoImplicit false

namespace ClaudePaper4

open BackfillPaper4 CodexPaper4 CodexPaper4.TriangleFreeEnumerationCore
  CodexPaper4.TriangleFreeEnumerationFamily

theorem parent_all (i : Fin 59) (S : Finset (Fin 7)) (hne : S.Nonempty)
    (hi : (reps 7 i).IsIndepSet (S : Set (Fin 7))) :
    ¬ Challenge.IsMedian (augment (reps 7 i) S) ∨
      ∃ j : Fin 69, Nonempty (augment (reps 7 i) S ≃g L8 j) := by
  fin_cases i
  · exact MedianEightParent00.parent_prop S hne hi
  · exact MedianEightParent01.parent_prop S hne hi
  · exact MedianEightParent02.parent_prop S hne hi
  · exact MedianEightParent03.parent_prop S hne hi
  · exact MedianEightParent04.parent_prop S hne hi
  · exact MedianEightParent05.parent_prop S hne hi
  · exact MedianEightParent06.parent_prop S hne hi
  · exact MedianEightParent07.parent_prop S hne hi
  · exact MedianEightParent08.parent_prop S hne hi
  · exact MedianEightParent09.parent_prop S hne hi
  · exact MedianEightParent10.parent_prop S hne hi
  · exact MedianEightParent11.parent_prop S hne hi
  · exact MedianEightParent12.parent_prop S hne hi
  · exact MedianEightParent13.parent_prop S hne hi
  · exact MedianEightParent14.parent_prop S hne hi
  · exact MedianEightParent15.parent_prop S hne hi
  · exact MedianEightParent16.parent_prop S hne hi
  · exact MedianEightParent17.parent_prop S hne hi
  · exact MedianEightParent18.parent_prop S hne hi
  · exact MedianEightParent19.parent_prop S hne hi
  · exact MedianEightParent20.parent_prop S hne hi
  · exact MedianEightParent21.parent_prop S hne hi
  · exact MedianEightParent22.parent_prop S hne hi
  · exact MedianEightParent23.parent_prop S hne hi
  · exact MedianEightParent24.parent_prop S hne hi
  · exact MedianEightParent25.parent_prop S hne hi
  · exact MedianEightParent26.parent_prop S hne hi
  · exact MedianEightParent27.parent_prop S hne hi
  · exact MedianEightParent28.parent_prop S hne hi
  · exact MedianEightParent29.parent_prop S hne hi
  · exact MedianEightParent30.parent_prop S hne hi
  · exact MedianEightParent31.parent_prop S hne hi
  · exact MedianEightParent32.parent_prop S hne hi
  · exact MedianEightParent33.parent_prop S hne hi
  · exact MedianEightParent34.parent_prop S hne hi
  · exact MedianEightParent35.parent_prop S hne hi
  · exact MedianEightParent36.parent_prop S hne hi
  · exact MedianEightParent37.parent_prop S hne hi
  · exact MedianEightParent38.parent_prop S hne hi
  · exact MedianEightParent39.parent_prop S hne hi
  · exact MedianEightParent40.parent_prop S hne hi
  · exact MedianEightParent41.parent_prop S hne hi
  · exact MedianEightParent42.parent_prop S hne hi
  · exact MedianEightParent43.parent_prop S hne hi
  · exact MedianEightParent44.parent_prop S hne hi
  · exact MedianEightParent45.parent_prop S hne hi
  · exact MedianEightParent46.parent_prop S hne hi
  · exact MedianEightParent47.parent_prop S hne hi
  · exact MedianEightParent48.parent_prop S hne hi
  · exact MedianEightParent49.parent_prop S hne hi
  · exact MedianEightParent50.parent_prop S hne hi
  · exact MedianEightParent51.parent_prop S hne hi
  · exact MedianEightParent52.parent_prop S hne hi
  · exact MedianEightParent53.parent_prop S hne hi
  · exact MedianEightParent54.parent_prop S hne hi
  · exact MedianEightParent55.parent_prop S hne hi
  · exact MedianEightParent56.parent_prop S hne hi
  · exact MedianEightParent57.parent_prop S hne hi
  · exact MedianEightParent58.parent_prop S hne hi

theorem covers7 : Covers (reps 7) :=
  covers_through_seven repCount reps (covers_one (reps 1) 0) TriangleFreeEnumerationLayers.layers
    7 (by norm_num) le_rfl

theorem cover8 (V : Type) [Fintype V] (G : SimpleGraph V) (hcard : Fintype.card V = 8)
    (hm : Challenge.IsMedian G) : ∃ j : Fin 69, Nonempty (G ≃g L8 j) := by
  classical
  have hc := hm.1
  have ht : G.CliqueFree 3 := check_Sec4_median_triangleFree V G hm
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := hc.exists_connected_induce_compl_singleton_of_finite_nontrivial
  have hsum : Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
    let e0 : ({v}ᶜ : Set V) ≃ {b : V // b ≠ v} := {
      toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
    have hop : Fintype.card {b : V // b ≠ v} + 1 = Fintype.card V := by
      simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe v)
    exact (congrArg (fun k : ℕ => k + 1) (Fintype.card_congr e0)).trans hop
  have hdel : Fintype.card ({v}ᶜ : Set V) = 7 := by omega
  have htri : (G.induce {v}ᶜ).CliqueFree 3 := by
    intro t hcl
    exact ht _ ((SimpleGraph.isNClique_induce_iff (G := G) {v}ᶜ t 3).mp hcl)
  obtain ⟨i, ⟨e⟩⟩ := covers7 ({v}ᶜ : Set V) (G.induce {v}ᶜ) hdel hv htri
  have hS : (liftedNeighbors G v (reps 7 i) e).Nonempty :=
    liftedNeighbors_nonempty G hc v (reps 7 i) e
  have hI := liftedNeighbors_independent G ht v (reps 7 i) e
  rcases parent_all i _ hS hI with hnm | ⟨j, ⟨f⟩⟩
  · exact absurd ((MedianMetricTransport.isMedian_iff (augmentationIso G v (reps 7 i) e)).mpr hm) hnm
  · exact ⟨j, ⟨(augmentationIso G v (reps 7 i) e).symm.trans f⟩⟩

theorem check_TheoremA_unique : Challenge.TheoremA_unique := by
  intro V _ G hcard hm hq
  obtain ⟨j, ⟨e⟩⟩ := cover8 V G hcard hm
  rcases L8_q j with ⟨h3, _⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact absurd ((MedianMetricTransport.question3'_iff e hm.1).mpr h3) hq
  · exact ⟨e.trans f⟩
  · exact absurd ((MedianMetricTransport.question3'_iff (e.trans f) hm.1).mpr check_Sec8_open.2) hq

theorem check_TheoremB_unique : Challenge.TheoremB_unique := by
  intro V _ G hcard hm
  have part1 : ¬ Challenge.Question4 G → Nonempty (G ≃g Challenge.G2) := by
    intro hq
    obtain ⟨j, ⟨e⟩⟩ := cover8 V G hcard hm
    rcases L8_q j with ⟨_, h4⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact absurd ((MedianMetricTransport.question4_iff e hm.1).mpr h4) hq
    · exact absurd ((MedianMetricTransport.question4_iff (e.trans f) hm.1).mpr check_Sec8_open.1) hq
    · exact ⟨e.trans f⟩
  exact ⟨part1, fun hq' => part1 (fun h4 => hq' (check_Sec2_Q4_imp_Q4' V G hm.1 h4))⟩

#print axioms cover8
#print axioms check_TheoremA_unique
#print axioms check_TheoremB_unique

end ClaudePaper4
