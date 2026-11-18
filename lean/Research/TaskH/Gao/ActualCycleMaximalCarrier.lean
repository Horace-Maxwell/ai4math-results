import Research.TaskH.Gao.ActualCycleFromSpokes
import Research.TaskH.Gao.ActualCycleSupportTwoConnected
import Research.TaskH.Gao.MaximalRegionActualAttachments

/-! Actual finite maximum cardinality supplies inclusion-maximal ordinary
carriers. The final deleted-component wrapper supplies its cycle internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem exists_maximal_twoConnected_superset [Fintype V] (G : SimpleGraph V)
    (L : Set V) [Fintype L] (hL : TwoConnected (G.induce L)) :
    ∃ (S : Set V) (iS : Fintype S), L ⊆ S ∧
      @TwoConnected S iS (G.induce S) ∧
      ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
        @TwoConnected T iT (G.induce T) → T ⊆ S := by
  classical
  let F : Finset (Set V) := Finset.univ.filter (fun T =>
    L ⊆ T ∧ ∃ iT : Fintype T, @TwoConnected T iT (G.induce T))
  have hLF : L ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_univ L, Set.Subset.rfl, inferInstance, hL⟩
  obtain ⟨S, hSF, hmax⟩ := Finset.exists_max_image F (fun T => T.ncard) ⟨L, hLF⟩
  obtain ⟨hLS, iS, hS⟩ := (Finset.mem_filter.mp hSF).2
  refine ⟨S, iS, hLS, hS, ?_⟩
  intro T iT hST hT
  have hTF : T ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_univ T, hLS.trans hST, iT, hT⟩
  have hcard : T.ncard ≤ S.ncard := hmax T hTF
  have he : S = T := Set.eq_of_subset_of_ncard_le hST hcard (Set.toFinite T)
  exact he.symm.subset

theorem actual_cycle_maximal_carrier [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (z : V) (c : G.Walk z z) (hc : c.IsCycle) :
    ∃ (S : Set V) (iS : Fintype S), z ∈ S ∧
      @TwoConnected S iS (G.induce S) ∧
      (∀ (T : Set V) (iT : Fintype T), S ⊆ T →
        @TwoConnected T iT (G.induce T) → T ⊆ S) ∧
      SingleAttachmentCarrier G S := by
  classical
  let L : Set V := {v | v ∈ c.support}
  obtain ⟨iL, hL⟩ := actual_cycle_support_twoConnected G z c hc
  let : Fintype L := iL
  obtain ⟨S, iS, hLS, hS, hmax⟩ := exists_maximal_twoConnected_superset G L hL
  let : Fintype S := iS
  exact ⟨S, iS, hLS c.start_mem_support, hS, hmax,
    maximal_twoConnected_region_single_attachment G S hG hS hmax⟩

theorem actual_component_two_spokes_maximal_carrier [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (z : V)
    (D : (G.induce {v | v ≠ z}).ConnectedComponent) (a b : D.supp)
    (hab : a ≠ b) (eza : G.Adj z a.1.1) (ezb : G.Adj z b.1.1) :
    ∃ (S : Set V) (iS : Fintype S), z ∈ S ∧
      @TwoConnected S iS (G.induce S) ∧
      (∀ (T : Set V) (iT : Fintype T), S ⊆ T →
        @TwoConnected T iT (G.induce T) → T ⊆ S) ∧
      SingleAttachmentCarrier G S := by
  obtain ⟨c, hc, _hsupport⟩ := actual_component_two_spokes_cycle G z D a b hab eza ezb
  exact actual_cycle_maximal_carrier G hG z c hc

#print axioms exists_maximal_twoConnected_superset
#print axioms actual_cycle_maximal_carrier
#print axioms actual_component_two_spokes_maximal_carrier
end TaskH.Gao
