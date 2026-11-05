import Research.Backfill.Paper7.ChallengeV2

/-! Source-only generic graph helpers for the frozen unicyclic predicate.
No main Corollary31, general order classification, or acceptance is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Unicyclic
open SimpleGraph BackfillPaper7.Challenge

theorem cycleEdgeSet_card {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {ell : ℕ} {s : Finset (Sym2 V)} (hs : s ∈ cycleEdgeSets G ell) :
    s.card = ell := by
  obtain ⟨u, w, hw, hlen, rfl⟩ := hs
  rw [List.toFinset_card_of_nodup hw.isTrail.edges_nodup,
    Walk.length_edges, hlen]
#print axioms Paper7Unicyclic.cycleEdgeSet_card

theorem unicyclic_cycle_unique_data {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {b : ℕ} (hG : IsUnicyclicWithCycle G b) :
    ∃ s ∈ cycleEdgeSets G b, ∀ ell t, t ∈ cycleEdgeSets G ell →
      ell = b ∧ t = s := by
  obtain ⟨s, hs, huniq⟩ := hG.2
  refine ⟨s, hs, ?_⟩
  intro ell t ht
  have heq := huniq ell t ht
  have hcard := congrArg Finset.card heq
  rw [cycleEdgeSet_card ht, cycleEdgeSet_card hs] at hcard
  exact ⟨hcard, heq⟩
#print axioms Paper7Unicyclic.unicyclic_cycle_unique_data

theorem unicyclic_three_le {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {b : ℕ} (hG : IsUnicyclicWithCycle G b) : 3 ≤ b := by
  obtain ⟨s, hs, _⟩ := hG.2
  obtain ⟨u, w, hw, hlen, _⟩ := hs
  simpa only [hlen] using hw.three_le_length
#print axioms Paper7Unicyclic.unicyclic_three_le

theorem unicyclic_cycleCount {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {b : ℕ} (hG : IsUnicyclicWithCycle G b) (ell : ℕ) :
    cycleCount G ell = if ell = b then 1 else 0 := by
  obtain ⟨s, hs, huniq⟩ := unicyclic_cycle_unique_data hG
  by_cases hell : ell = b
  · subst ell
    have hset : cycleEdgeSets G b = {s} := by
      ext t
      constructor
      · intro ht
        exact Set.mem_singleton_iff.mpr (huniq b t ht).2
      · rintro rfl
        exact hs
    simp only [cycleCount, hset, Set.ncard_singleton, ite_true]
  · have hset : cycleEdgeSets G ell = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hell (huniq ell t ht).1
    simp only [cycleCount, hset, Set.ncard_empty, ite_eq_right hell]
#print axioms Paper7Unicyclic.unicyclic_cycleCount

theorem unicyclic_isOddGirth {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {b : ℕ} (hG : IsUnicyclicWithCycle G b) (hb : Odd b) :
    IsOddGirth G b := by
  obtain ⟨s, hs, huniq⟩ := unicyclic_cycle_unique_data hG
  refine ⟨hb, ?_, ?_⟩
  · obtain ⟨u, w, hw, hlen, _⟩ := hs
    exact ⟨u, w, hw, hlen⟩
  · intro u w hw _
    exact le_of_eq ((huniq w.length w.edges.toFinset ⟨u,w,hw,rfl,rfl⟩).1.symm)
#print axioms Paper7Unicyclic.unicyclic_isOddGirth
end Paper7Unicyclic
