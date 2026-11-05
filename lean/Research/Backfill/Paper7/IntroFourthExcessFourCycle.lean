import Research.Backfill.Paper7.IntroNoDoubleCommonFourthBound
import Research.Backfill.Paper7.CycleFirstDart

/-! An excess fourth moment gives two actual distinct common neighbors.
Their concrete quad walk is the unique real cycle, including its support. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroFourCycleBridge
open SimpleGraph BackfillPaper7.Challenge Paper7FourWalks Paper7UnicyclicSchwenk

theorem unicyclic_fourth_excess_forces_four_cycle
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (v : V)
    (hlarge : (G.degree v : ℝ) ^ 2 + Fintype.card V - (G.degree v : ℝ) - 1 <
      ((G.adjMatrix ℝ) ^ 4) v v) :
    b = 4 ∧ ∃ p j q : V,
      v ≠ p ∧ v ≠ j ∧ v ≠ q ∧ p ≠ j ∧ p ≠ q ∧ j ≠ q ∧
      G.Adj v p ∧ G.Adj p j ∧ G.Adj j q ∧ G.Adj q v ∧
      (∀ z : V, z ∈ w.support ↔ z = v ∨ z = p ∨ z = j ∨ z = q) ∧
      (∀ t : V, (G.Adj v t ∧ G.Adj t j) ↔ t = p ∨ t = q) := by
  have hex : ∃ j p q : V, j ≠ v ∧ p ≠ q ∧
      G.Adj v p ∧ G.Adj p j ∧ G.Adj v q ∧ G.Adj q j := by
    by_contra hno
    have hcommon : ∀ j, j ≠ v →
        ((G.neighborFinset v).filter (fun a => G.Adj a j)).card ≤ 1 := by
      intro j hj
      apply Finset.card_le_one.mpr
      intro p hp q hq
      obtain ⟨hpN, hpj⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqN, hqj⟩ := Finset.mem_filter.mp hq
      by_contra hpq
      exact hno ⟨j, p, q, hj, hpq, (G.mem_neighborFinset v p).mp hpN,
        hpj, (G.mem_neighborFinset v q).mp hqN, hqj⟩
    have hupper := fourth_moment_upper_of_no_double_common_neighbors G htriangle v hcommon
    exact (not_lt_of_ge hupper) hlarge
  obtain ⟨j, p, q, hjv, hpq, hvp, hpj, hvq, hqj⟩ := hex
  let quad : Quad G := ⟨(v, p, j, q), hvp, hpj, hqj.symm, hvq.symm⟩
  have hquad : (quadWalk G quad).IsCycle :=
    (quadWalk_isCycle_iff G quad).mpr ⟨hjv.symm, hpq⟩
  obtain ⟨s, _hs, huniq⟩ := hG.2
  have hwE : w.edges.toFinset = s := huniq b _ ⟨r, w, hw, hlen, rfl⟩
  have hqE : (quadWalk G quad).edges.toFinset = s :=
    huniq 4 _ ⟨v, quadWalk G quad, hquad, rfl, rfl⟩
  have hsupp : {z | z ∈ w.support} = {z | z ∈ (quadWalk G quad).support} :=
    cycle_support_eq_of_edgeFinset w (quadWalk G quad) hw hquad (hwE.trans hqE.symm)
  have hfin : w.support.toFinset = (quadWalk G quad).support.toFinset := by
    ext z
    simpa only [List.mem_toFinset, Set.mem_ofPred_eq] using Set.ext_iff.mp hsupp z
  have hlen4 : w.length = 4 := by
    calc
      w.length = w.support.toFinset.card := (Paper7Cycles.cycle_support_card w hw).symm
      _ = (quadWalk G quad).support.toFinset.card := congrArg Finset.card hfin
      _ = (quadWalk G quad).length := Paper7Cycles.cycle_support_card (quadWalk G quad) hquad
      _ = 4 := rfl
  refine ⟨by omega, p, j, q, hvp.ne, hjv.symm, hvq.ne, hpj.ne, hpq,
    hqj.symm.ne, hvp, hpj, hqj.symm, hvq.symm, ?_, ?_⟩
  · intro z
    have hz : z ∈ w.support ↔ z ∈ (quadWalk G quad).support := Set.ext_iff.mp hsupp z
    rw [hz]
    simp only [quadWalk, quad, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro t
    constructor
    · intro ht
      exact Paper7IntroTwoWalkCollision.unicyclic_common_neighbor_pair
        G b hG v j p q hjv.symm hpq hvp hpj hvq hqj t ht.1 ht.2
    · intro ht
      rcases ht with htp | htq
      · rw [htp]
        exact ⟨hvp, hpj⟩
      · rw [htq]
        exact ⟨hvq, hqj⟩
#print axioms Paper7IntroFourCycleBridge.unicyclic_fourth_excess_forces_four_cycle

end Paper7IntroFourCycleBridge
