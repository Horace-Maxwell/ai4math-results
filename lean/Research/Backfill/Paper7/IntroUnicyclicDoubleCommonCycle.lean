import Research.Backfill.Paper7.IntroUnicyclicTwoWalkCollision
import Research.Backfill.Paper7.CycleFirstDart
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! Source-only candidate. Two actual common neighbors determine the original
unique cycle. No moment, order, integral-spectrum or support-cover premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTwoStepTopology
open SimpleGraph BackfillPaper7.Challenge Paper7FourWalks Paper7UnicyclicSchwenk

theorem unicyclic_double_common_forces_four_cycle
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (c p j q : V) (hcj : c ≠ j) (hpq : p ≠ q)
    (hcp : G.Adj c p) (hpj : G.Adj p j)
    (hcq : G.Adj c q) (hqj : G.Adj q j) :
    b = 4 ∧
      (∀ z : V, z ∈ w.support ↔ z = c ∨ z = p ∨ z = j ∨ z = q) ∧
      (∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p ∨ t = q) ∧
      (G.neighborFinset c).filter (fun t => G.Adj t j) = {p, q} ∧
      ((G.adjMatrix ℝ) ^ 2) c j = 2 ∧ ((G.adjMatrix ℝ) ^ 2) j c = 2 ∧
      ¬ G.Adj c j ∧ ¬ G.Adj p q := by
  let quad : Quad G := ⟨(c, p, j, q), hcp, hpj, hqj.symm, hcq.symm⟩
  have hquad : (quadWalk G quad).IsCycle :=
    (quadWalk_isCycle_iff G quad).mpr ⟨hcj, hpq⟩
  obtain ⟨s, _hs, huniq⟩ := hG.2
  have hwE : w.edges.toFinset = s := huniq b _ ⟨r, w, hw, hlen, rfl⟩
  have hqE : (quadWalk G quad).edges.toFinset = s :=
    huniq 4 _ ⟨c, quadWalk G quad, hquad, rfl, rfl⟩
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
  have hb4 : b = 4 := hlen.symm.trans hlen4
  have hcommon : ∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p ∨ t = q := by
    intro t
    constructor
    · intro ht
      exact Paper7IntroTwoWalkCollision.unicyclic_common_neighbor_pair
        G b hG c j p q hcj hpq hcp hpj hcq hqj t ht.1 ht.2
    · rintro (htp | htq)
      · rw [htp]
        exact ⟨hcp, hpj⟩
      · rw [htq]
        exact ⟨hcq, hqj⟩
  have hfilter : (G.neighborFinset c).filter (fun t => G.Adj t j) = {p, q} := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    exact hcommon t
  have hA2 : ((G.adjMatrix ℝ) ^ 2) c j = 2 := by
    rw [Paper7IntroPendantFour.adjacency_square_common_card, hfilter,
      Finset.card_pair hpq]
    norm_num
  have hA2rev : ((G.adjMatrix ℝ) ^ 2) j c = 2 :=
    ((G.isSymm_adjMatrix.pow 2).apply c j).trans hA2
  have heven : Even b := by rw [hb4]; exact ⟨2, rfl⟩
  have htri := Paper7IntroTwoWalkCollision.even_unicyclic_no_triangle G b hG heven
  refine ⟨hb4, ?_, hcommon, hfilter, hA2, hA2rev, ?_, ?_⟩
  · intro z
    have hz : z ∈ w.support ↔ z ∈ (quadWalk G quad).support := Set.ext_iff.mp hsupp z
    rw [hz]
    simp only [quadWalk, quad, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro hcj'
    exact htri c p j hcp hpj hcj'.symm
  · intro hpq'
    exact htri c p q hcp hpq' hcq.symm
#print axioms Paper7IntroTwoStepTopology.unicyclic_double_common_forces_four_cycle

theorem unicyclic_nonfour_two_step_fibre
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b ≠ 4) (c p j : V) (hcj : c ≠ j)
    (hcp : G.Adj c p) (hpj : G.Adj p j) :
    (∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p) ∧
      (G.neighborFinset c).filter (fun t => G.Adj t j) = {p} ∧
      ((G.adjMatrix ℝ) ^ 2) c j = 1 ∧ ((G.adjMatrix ℝ) ^ 2) j c = 1 := by
  have hcommon : ∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p := by
    intro t
    constructor
    · intro ht
      by_contra htp
      exact hb4 (unicyclic_double_common_forces_four_cycle G b hG r w hw hlen
        c p j t hcj (Ne.symm htp) hcp hpj ht.1 ht.2).1
    · intro htp
      rw [htp]
      exact ⟨hcp, hpj⟩
  have hfilter : (G.neighborFinset c).filter (fun t => G.Adj t j) = {p} := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact hcommon t
  have hA2 : ((G.adjMatrix ℝ) ^ 2) c j = 1 := by
    rw [Paper7IntroPendantFour.adjacency_square_common_card, hfilter, Finset.card_singleton]
    norm_num
  exact ⟨hcommon, hfilter, hA2, ((G.isSymm_adjMatrix.pow 2).apply c j).trans hA2⟩
#print axioms Paper7IntroTwoStepTopology.unicyclic_nonfour_two_step_fibre

end Paper7IntroTwoStepTopology
