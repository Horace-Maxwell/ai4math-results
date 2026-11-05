import Research.Backfill.Paper7.IntroFourCycleFiniteParity
import Research.Backfill.Paper7.IntroPureFourLeafPerronColumn
import Research.Backfill.Paper7.IntroAttachmentFourLeafCycle
import Research.Backfill.Paper7.IntroAttachmentLeafStarShape

/-! The original four-leaf/six-degree branch is impossible. Complete star
families are obtained separately at every actual off-cycle neighbor, in its
actual deleted-cycle connected component. Only one Perron witness is selected.
This candidate is uncompiled; actual parent production is bound separately. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourLeafExclusion
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroFourCycleWeights Paper7IntroFourLeafColumn
open Paper7IntroFourCycleBridge Paper7IntroAttachmentLeafStar Paper7IntroTwoWalkCollision

theorem intro21_even_attachment_not_four_leaves_degree_six
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ¬ (((G.neighborFinset a.val.val).erase c.val).card = 4 ∧ G.degree c.val = 6) := by
  rintro ⟨hm4, hd6⟩
  obtain ⟨Y, i₀, eps, f, _hY, _hY4, _haD, _hacne, _hinj, _hdata, _hcover,
      _hNa, _hNl, _heps, hflip, hf, hAf, _hfi, _hfY, _hfa, hfc, _hN,
      _hQ0, _hM6, _hP4, _hK, _hS, hcol⟩ :=
    intro21_even_four_leaf_degree_six_perron_column
      G b hG hI hn hb r w hw hlen C a c hac hm4 hd6
  obtain ⟨_hb4, p, j, q, _hcp, hcj, _hcq, _hpj, hpq, _hjq,
      hcpA, hpjA, hjqA, hqcA, hs, hcommon⟩ :=
    intro21_even_four_leaf_degree_six_cycle
      G b hG hI hn hb r w hw hlen C a c hac hm4 hd6
  have htriangle := even_unicyclic_no_triangle G b hG hb
  have hnotcj : ¬ G.Adj c.val j := by
    intro hcjA
    exact htriangle c.val p j hcpA hpjA hcjA.symm
  have hjS : j ∈ w.support := (hs j).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hsignj : eps j = eps c.val := by
    linarith only [hflip c.val p hcpA, hflip j p hpjA.symm]
  have hcommonFin : (G.neighborFinset j).filter (fun t => G.Adj t c.val) = {p, q} := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hjt, htc⟩
      exact (hcommon t).mp ⟨htc.symm, hjt.symm⟩
    · rintro (htp | htq)
      · rw [htp]
        exact ⟨hpjA.symm, hcpA.symm⟩
      · rw [htq]
        exact ⟨hjqA, hqcA⟩
  have hBjc : ((G.adjMatrix ℝ) ^ 2) j c.val = 2 := by
    rw [pow_two, G.adjMatrix_mul_apply]
    simp only [G.adjMatrix_apply]
    rw [← Finset.sum_filter, hcommonFin, Finset.sum_pair hpq]
    norm_num
  have hfj : f j = 2 := (hcol j hsignj hcj.symm).symm.trans hBjc
  have hstar (v : V) (hv : v ∈ w.support) (x : V) (hx : x ∉ w.support)
      (hxv : G.Adj x v) :
      ∃ T : Finset V, v ∉ T ∧ G.neighborFinset x = insert v T ∧
        ∀ y ∈ T, ∀ t, G.Adj y t ↔ t = x := by
    let xo : {t : V // t ∉ w.support} := ⟨x, hx⟩
    let Cx := (deleteVertices G {t | t ∈ w.support}).connectedComponentMk xo
    let ax : Cx.supp := ⟨xo, ConnectedComponent.connectedComponentMk_mem⟩
    let cv : {t : V // t ∈ w.support} := ⟨v, hv⟩
    obtain ⟨T, hT, _hd, _hne, _hinj, _hdata, _hcover, _hNx, hNl⟩ :=
      intro21_even_actual_attachment_leaf_star G b hG hI hn hb r w hw hlen
        Cx ax cv hxv
    change T = (G.neighborFinset x).erase v at hT
    refine ⟨T, ?_, ?_, ?_⟩
    · rw [hT]
      exact Finset.notMem_erase v (G.neighborFinset x)
    · rw [hT]
      exact (Finset.insert_erase ((G.mem_neighborFinset x v).mpr hxv)).symm
    · intro y hy t
      exact hNl ⟨y, hy⟩ t
  have hstarsC : ∀ x, G.Adj c.val x → x ≠ p → x ≠ q →
      ∃ T : Finset V, c.val ∉ T ∧ G.neighborFinset x = insert c.val T ∧
        ∀ y ∈ T, ∀ t, G.Adj y t ↔ t = x := by
    intro x hcx hxp hxq
    have hxout : x ∉ w.support := by
      intro hxS
      rcases (hs x).mp hxS with hxc | hxp' | hxj | hxq'
      · exact hcx.ne hxc.symm
      · exact hxp hxp'
      · apply hnotcj
        simpa only [hxj] using hcx
      · exact hxq hxq'
    exact hstar c.val c.property x hxout hcx.symm
  have hstarsJ : ∀ x, G.Adj j x → x ≠ p → x ≠ q →
      ∃ T : Finset V, j ∉ T ∧ G.neighborFinset x = insert j T ∧
        ∀ y ∈ T, ∀ t, G.Adj y t ↔ t = x := by
    intro x hjx hxp hxq
    have hxout : x ∉ w.support := by
      intro hxS
      rcases (hs x).mp hxS with hxc | hxp' | hxj | hxq'
      · apply hnotcj
        exact (hxc ▸ hjx).symm
      · exact hxp hxp'
      · exact hjx.ne hxj.symm
      · exact hxq hxq'
    exact hstar j hjS x hxout hjx.symm
  exact four_cycle_column_star_parity_contradiction G eps f hflip hf hAf
    c.val p j q hpq hcpA hqcA.symm hpjA.symm hjqA hd6 hfc hfj
    (fun x hcx hjx => (hcommon x).mp ⟨hcx, hjx.symm⟩) hcol hstarsC hstarsJ
#print axioms Paper7IntroFourLeafExclusion.intro21_even_attachment_not_four_leaves_degree_six

end Paper7IntroFourLeafExclusion
