import Research.TaskH.Gao.ActualCycleMaximalCarrier
import Research.TaskH.Gao.TerminalCommonPointDeletedComponents
import Research.TaskH.Gao.CarrierGreatestRegion

/-! Real leaf deletion confines every non-y component. Two genuine remaining
spokes yield an internally chosen maximal ordinary two-connected carrier. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_terminal_deleted_component_avoids_leaf
    (G : SimpleGraph V) (y z a : V) (hT : TerminalFragment G {y} z)
    (hay : a ≠ y) (haz : a ≠ z) :
    y ∉ deletedInterior G z ((G.induce {v | v ≠ z}).connectedComponentMk ⟨a, haz⟩) := by
  rintro ⟨hyz, hyD⟩
  obtain ⟨q⟩ := ConnectedComponent.exact hyD
  have haY := terminal_walk_stays_without_boundary G {y} z hT q (Set.mem_singleton y)
  exact hay haY

theorem singleton_terminal_outside_ordinary_carrier [Fintype V]
    (G : SimpleGraph V) (y z : V) (hT : TerminalFragment G {y} z)
    (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S)) : y ∉ S := by
  classical
  intro hyS
  have hex : ∃ q ∈ S, q ≠ y ∧ q ≠ z := by
    by_contra hn
    have hsub : S ⊆ ({y, z} : Set V) := by
      intro q hq
      by_cases hqy : q = y
      · exact Or.inl hqy
      · right
        by_contra hqz
        exact hn ⟨q, hq, hqy, hqz⟩
    have hc := Set.ncard_le_ncard hsub
    have hp := Set.ncard_insert_le y ({z} : Set V)
    rw [Set.ncard_singleton] at hp
    have hs3 : 3 ≤ S.ncard := by
      simpa only [Set.fintypeCard_eq_ncard] using hS.1
    omega
  obtain ⟨q, hqS, hqy, hqz⟩ := hex
  have hyz : y ≠ z := fun he => hT.2.1 (show z ∈ ({y} : Set V) from he.symm)
  obtain ⟨p⟩ := twoConnected_region_reachable_avoiding G S hS z ⟨y, hyS⟩ ⟨q, hqS⟩ hyz hqz
  exact hqy (terminal_walk_stays_without_boundary G {y} z hT p (Set.mem_singleton y))

theorem singleton_terminal_high_degree_actual_carrier [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (y p z : V)
    (hT : TerminalFragment G {y} z)
    (hcommon : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (hhigh : 3 ≤ (G.neighborSet z).ncard) :
    ∃ (S : Set V) (iS : Fintype S), z ∈ S ∧
      @TwoConnected S iS (G.induce S) ∧
      (∀ (T : Set V) (iT : Fintype T), S ⊆ T →
        @TwoConnected T iT (G.induce T) → T ⊆ S) ∧
      SingleAttachmentCarrier G S := by
  classical
  obtain ⟨a, eza, hay⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < (G.neighborSet z).ncard by omega) y
  have hex : ∃ b ∈ G.neighborSet z, b ≠ y ∧ b ≠ a := by
    by_contra hn
    have hsub : G.neighborSet z ⊆ ({y, a} : Set V) := by
      intro b hb
      by_cases hby : b = y
      · exact Or.inl hby
      · right
        by_contra hba
        exact hn ⟨b, hb, hby, hba⟩
    have hc := Set.ncard_le_ncard hsub
    have hp := Set.ncard_insert_le y ({a} : Set V)
    rw [Set.ncard_singleton] at hp
    omega
  obtain ⟨b, ezb, hby, hba⟩ := hex
  have haz : a ≠ z := eza.ne'
  have hbz : b ≠ z := ezb.ne'
  let D := (G.induce {v | v ≠ z}).connectedComponentMk ⟨a, haz⟩
  let E := (G.induce {v | v ≠ z}).connectedComponentMk ⟨b, hbz⟩
  have hyD : y ∉ deletedInterior G z D :=
    singleton_terminal_deleted_component_avoids_leaf G y z a hT hay haz
  have hyE : y ∉ deletedInterior G z E :=
    singleton_terminal_deleted_component_avoids_leaf G y z b hT hby hbz
  have hED : E = D := terminal_common_point_deleted_component_unique G y p z hG hcommon E D hyE hyD
  let ar : D.supp := ⟨⟨a, haz⟩, rfl⟩
  let br : D.supp := ⟨⟨b, hbz⟩, hED⟩
  have hab : ar ≠ br := fun he => hba (congrArg (fun v : D.supp => v.1.1) he).symm
  exact actual_component_two_spokes_maximal_carrier G hG z D ar br hab eza ezb

#print axioms singleton_terminal_deleted_component_avoids_leaf
#print axioms singleton_terminal_outside_ordinary_carrier
#print axioms singleton_terminal_high_degree_actual_carrier
end TaskH.Gao
