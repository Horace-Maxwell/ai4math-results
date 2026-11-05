import Research.Backfill.Paper7.IntroUnicyclicDoubleCommonCycle
import Research.Backfill.Paper7.IntroUnicyclicCycleCompleteNeighbors

/-! Source-only candidate. The single/double two-step alternatives use the
original circle itself, not a separately assumed four-cycle or support table. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTwoStepTopology
open SimpleGraph BackfillPaper7.Challenge Paper7FourWalks

theorem unicyclic_nonfour_circle_continuation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b ≠ 4) (c p : V) (hc : c ∈ w.support) (hp : p ∈ w.support)
    (hcp : G.Adj c p) :
    ∃ j : V, j ∈ w.support ∧ j ≠ c ∧ j ≠ p ∧ G.Adj p j ∧
      (∀ v, v ∈ w.support → (G.Adj p v ↔ v = c ∨ v = j)) ∧
      (∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p) ∧
      (G.neighborFinset c).filter (fun t => G.Adj t j) = {p} ∧
      ((G.adjMatrix ℝ) ^ 2) c j = 1 ∧ ((G.adjMatrix ℝ) ^ 2) j c = 1 := by
  obtain ⟨j, hj, hjc, hpj, hcomplete⟩ :=
    Paper7IntroCycleCompleteNeighbors.unicyclic_cycle_neighbor_continuation
      G b hG r w hw hlen p c hp hc hcp.symm
  obtain ⟨hcommon, hfilter, hA2, hA2rev⟩ :=
    unicyclic_nonfour_two_step_fibre G b hG r w hw hlen hb4 c p j
      (Ne.symm hjc) hcp hpj
  exact ⟨j, hj, hjc, hpj.ne.symm, hpj, hcomplete, hcommon, hfilter, hA2, hA2rev⟩
#print axioms Paper7IntroTwoStepTopology.unicyclic_nonfour_circle_continuation

theorem unicyclic_four_circle_at_vertex
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b = 4) (c : V) (hc : c ∈ w.support) :
    ∃ p j q : V,
      c ≠ p ∧ c ≠ j ∧ c ≠ q ∧ p ≠ j ∧ p ≠ q ∧ j ≠ q ∧
      G.Adj c p ∧ G.Adj p j ∧ G.Adj j q ∧ G.Adj q c ∧
      (∀ z : V, z ∈ w.support ↔ z = c ∨ z = p ∨ z = j ∨ z = q) ∧
      (∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p ∨ t = q) ∧
      (G.neighborFinset c).filter (fun t => G.Adj t j) = {p, q} ∧
      ((G.adjMatrix ℝ) ^ 2) c j = 2 ∧ ((G.adjMatrix ℝ) ^ 2) j c = 2 ∧
      ¬ G.Adj c j ∧ ¬ G.Adj p q := by
  let wr := w.rotate c hc
  have hwr : wr.IsCycle := hw.rotate hc
  have hwr4 : wr.length = 4 := by
    calc
      wr.length = w.length := Walk.length_rotate w c hc
      _ = b := hlen
      _ = 4 := hb4
  let quad := quadOfClosed G c wr hwr4
  have hquad : (quadWalk G quad).IsCycle := by
    change (quadWalk G (quadOfClosed G c wr hwr4)).IsCycle
    rw [quadWalk_ofClosed]
    exact hwr
  have hop := (quadWalk_isCycle_iff G quad).mp hquad
  have hcj : c ≠ wr.getVert 2 := hop.1
  have hpq : wr.getVert 1 ≠ wr.getVert 3 := hop.2
  have hcp : G.Adj c (wr.getVert 1) := quad.property.1
  have hpj : G.Adj (wr.getVert 1) (wr.getVert 2) := quad.property.2.1
  have hjq : G.Adj (wr.getVert 2) (wr.getVert 3) := quad.property.2.2.1
  have hqc : G.Adj (wr.getVert 3) c := quad.property.2.2.2
  obtain ⟨_hb4, hsupp, hcommon, hfilter, hA2, hA2rev, hnotcj, hnotpq⟩ :=
    unicyclic_double_common_forces_four_cycle G b hG r w hw hlen
      c (wr.getVert 1) (wr.getVert 2) (wr.getVert 3) hcj hpq
      hcp hpj hqc.symm hjq.symm
  exact ⟨wr.getVert 1, wr.getVert 2, wr.getVert 3,
    hcp.ne, hcj, hqc.ne.symm, hpj.ne, hpq, hjq.ne, hcp, hpj, hjq, hqc,
    hsupp, hcommon, hfilter, hA2, hA2rev, hnotcj, hnotpq⟩
#print axioms Paper7IntroTwoStepTopology.unicyclic_four_circle_at_vertex

theorem unicyclic_four_circle_from_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b = 4) (c p q : V) (hc : c ∈ w.support)
    (hp : p ∈ w.support) (hq : q ∈ w.support) (hpq : p ≠ q)
    (hcp : G.Adj c p) (hcq : G.Adj c q) :
    ∃ j : V, j ∈ w.support ∧ j ≠ c ∧ j ≠ p ∧ j ≠ q ∧
      G.Adj p j ∧ G.Adj q j ∧ ¬ G.Adj c j ∧
      (∀ z : V, z ∈ w.support ↔ z = c ∨ z = p ∨ z = j ∨ z = q) ∧
      (∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p ∨ t = q) ∧
      (G.neighborFinset c).filter (fun t => G.Adj t j) = {p, q} ∧
      ((G.adjMatrix ℝ) ^ 2) c j = 2 ∧ ((G.adjMatrix ℝ) ^ 2) j c = 2 ∧
      (∀ v, v ∈ w.support → (G.Adj j v ↔ v = p ∨ v = q)) := by
  obtain ⟨p₀, j, q₀, _hcp₀, hcj, _hcq₀, _hp₀j, hp₀q₀, _hjq₀,
    _hcp₀A, _hp₀jA, _hjq₀A, _hq₀cA, hsupp, hcommon, hfilter, hA2, hA2rev,
    hnotcj, _hnotpq⟩ := unicyclic_four_circle_at_vertex G b hG r w hw hlen hb4 c hc
  have hpp : p = p₀ ∨ p = q₀ := by
    rcases (hsupp p).mp hp with hpc | hpp | hpj | hpq₀
    · exact (hcp.ne hpc.symm).elim
    · exact Or.inl hpp
    · exact (hnotcj (hpj ▸ hcp)).elim
    · exact Or.inr hpq₀
  have hqq : q = p₀ ∨ q = q₀ := by
    rcases (hsupp q).mp hq with hqc | hqp | hqj | hqq
    · exact (hcq.ne hqc.symm).elim
    · exact Or.inl hqp
    · exact (hnotcj (hqj ▸ hcq)).elim
    · exact Or.inr hqq
  have hpair : ({p, q} : Finset V) = {p₀, q₀} := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      rcases ht with htp | htq
      · rw [htp]
        exact hpp
      · rw [htq]
        exact hqq
    · rw [Finset.card_pair hp₀q₀, Finset.card_pair hpq]
  have hperm : ∀ t : V, (t = p₀ ∨ t = q₀) ↔ (t = p ∨ t = q) := by
    intro t
    have hh := congrArg (fun s : Finset V => t ∈ s) hpair.symm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using Iff.of_eq hh
  have hpjA : G.Adj p j := ((hcommon p).mpr hpp).2
  have hqjA : G.Adj q j := ((hcommon q).mpr hqq).2
  have hsupp' : ∀ z : V, z ∈ w.support ↔ z = c ∨ z = p ∨ z = j ∨ z = q := by
    intro z
    constructor
    · intro hz
      rcases (hsupp z).mp hz with hzc | hzp | hzj | hzq
      · exact Or.inl hzc
      · rcases (hperm z).mp (Or.inl hzp) with hzp' | hzq'
        · exact Or.inr (Or.inl hzp')
        · exact Or.inr (Or.inr (Or.inr hzq'))
      · exact Or.inr (Or.inr (Or.inl hzj))
      · rcases (hperm z).mp (Or.inr hzq) with hzp' | hzq'
        · exact Or.inr (Or.inl hzp')
        · exact Or.inr (Or.inr (Or.inr hzq'))
    · intro hz
      apply (hsupp z).mpr
      rcases hz with hzc | hzp | hzj | hzq
      · exact Or.inl hzc
      · rcases (hperm z).mpr (Or.inl hzp) with hzp' | hzq'
        · exact Or.inr (Or.inl hzp')
        · exact Or.inr (Or.inr (Or.inr hzq'))
      · exact Or.inr (Or.inr (Or.inl hzj))
      · rcases (hperm z).mpr (Or.inr hzq) with hzp' | hzq'
        · exact Or.inr (Or.inl hzp')
        · exact Or.inr (Or.inr (Or.inr hzq'))
  have hcommon' : ∀ t : V, (G.Adj c t ∧ G.Adj t j) ↔ t = p ∨ t = q := by
    intro t
    exact (hcommon t).trans (hperm t)
  have hfilter' : (G.neighborFinset c).filter (fun t => G.Adj t j) = {p, q} :=
    hfilter.trans hpair.symm
  refine ⟨j, (hsupp' j).mpr (Or.inr (Or.inr (Or.inl rfl))), hcj.symm,
    hpjA.ne.symm, hqjA.ne.symm, hpjA, hqjA, hnotcj, hsupp', hcommon',
    hfilter', hA2, hA2rev, ?_⟩
  intro v hv
  constructor
  · intro hjv
    rcases (hsupp' v).mp hv with hvc | hvp | hvj | hvq
    · exact (hnotcj (hvc ▸ hjv).symm).elim
    · exact Or.inl hvp
    · exact (hjv.ne hvj.symm).elim
    · exact Or.inr hvq
  · rintro (hvp | hvq)
    · rw [hvp]
      exact hpjA.symm
    · rw [hvq]
      exact hqjA.symm
#print axioms Paper7IntroTwoStepTopology.unicyclic_four_circle_from_neighbors

end Paper7IntroTwoStepTopology
