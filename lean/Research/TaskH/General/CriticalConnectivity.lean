import Research.TaskH.General.CriticalColoring
import Research.TaskH.Fan.Challenge

/-! Full-criticality supplies actual connectedness after every single deletion. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open SimpleGraph TaskH.Challenge
variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

theorem critical_original_connected [Fintype V] (h : IsCriticalPlus k G) :
    G.Connected := by
  classical
  have hpos : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le k) (critical_card_gt h)
  let _ : Nonempty V := Fintype.card_pos_iff.mp hpos
  by_contra hn
  have hproper : ∀ C : G.ConnectedComponent, C.supp ≠ Set.univ := by
    intro C heq
    apply hn
    refine { preconnected := ?_, nonempty := inferInstance }
    intro a b
    exact C.reachable_of_mem_supp (by rw [heq]; trivial) (by rw [heq]; trivial)
  apply TaskH.critical_not_colorable h
  apply SimpleGraph.colorable_iff_forall_connectedComponent.mpr
  intro C
  exact critical_colorable_proper_induce h C.supp (hproper C)

theorem critical_deleted_connected [Fintype V] (hk : 2 ≤ k) (h : IsCriticalPlus k G)
    (z : V) : (G.induce {v | v ≠ z}).Connected := by
  classical
  have hcard := critical_card_gt h
  have hnot : ¬ (Finset.univ : Finset V) ⊆ {z} := by
    intro hs
    have hc := Finset.card_le_card hs
    have hc' : Fintype.card V ≤ 1 := by simpa only [Finset.card_univ, Finset.card_singleton] using hc
    omega
  obtain ⟨w, _hw, hw⟩ := Finset.not_subset.mp hnot
  have hwz : w ≠ z := by
    intro he
    exact hw (by simp only [he, Finset.mem_singleton])
  let J := G.induce {v | v ≠ z}
  have hne : Nonempty {v : V // v ≠ z} := ⟨⟨w, hwz⟩⟩
  by_contra hn
  have hbad : ∃ a b : {v : V // v ≠ z}, ¬J.Reachable a b := by
    by_contra hh
    apply hn
    refine { preconnected := ?_, nonempty := hne }
    intro a b
    by_contra hab
    exact hh ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hbad
  let S : Set V := {v | v = z ∨ ∃ hv : v ≠ z, J.Reachable a ⟨v, hv⟩}
  let T : Set V := {v | v = z ∨ v ∉ S}
  have hzS : z ∈ S := Or.inl rfl
  have hzT : z ∈ T := Or.inl rfl
  have haS : a.1 ∈ S := Or.inr ⟨a.2, ⟨SimpleGraph.Walk.nil⟩⟩
  have hbS : b.1 ∉ S := by
    rintro (he | ⟨_hb, hr⟩)
    · exact b.2 he
    · exact hab hr
  have haT : a.1 ∉ T := by
    rintro (he | ha)
    · exact a.2 he
    · exact ha haS
  have hsproper : S ≠ Set.univ := by
    intro he
    apply hbS
    rw [he]
    trivial
  have htproper : T ≠ Set.univ := by
    intro he
    apply haT
    rw [he]
    trivial
  have hcover : ∀ v : V, v ∈ S ∨ v ∈ T := by
    intro v
    by_cases hv : v ∈ S
    · exact Or.inl hv
    · exact Or.inr (Or.inr hv)
  have hinter : ∀ v : V, v ∈ S → v ∈ T → v = z := by
    intro v hs ht
    rcases ht with ht | ht
    · exact ht
    · exact False.elim (ht hs)
  have hclosed : ∀ v ∈ S, v ≠ z → ∀ t, G.Adj v t → t ∈ S := by
    intro v hv hvz t e
    by_cases htz : t = z
    · exact Or.inl htz
    · rcases hv with hv | ⟨_hv, hr⟩
      · exact False.elim (hvz hv)
      · exact Or.inr ⟨htz, hr.trans (show J.Adj ⟨v, hvz⟩ ⟨t, htz⟩ from e).reachable⟩
  have hedge : ∀ p q : V, G.Adj p q → (p ∈ S ∧ q ∈ S) ∨ (p ∈ T ∧ q ∈ T) := by
    intro p q e
    by_cases hp : p ∈ S
    · by_cases hq : q ∈ S
      · exact Or.inl ⟨hp, hq⟩
      · have hpz : p = z := by
          by_contra hpz
          exact hq (hclosed p hp hpz q e)
        exact Or.inr ⟨Or.inl hpz, Or.inr hq⟩
    · by_cases hq : q ∈ S
      · have hqz : q = z := by
          by_contra hqz
          exact hp (hclosed q hq hqz p e.symm)
        exact Or.inr ⟨Or.inr hp, Or.inl hqz⟩
      · exact Or.inr ⟨Or.inr hp, Or.inr hq⟩
  exact TaskH.critical_not_colorable h
    (colorable_glue_at_vertex G S T z hzS hzT hcover hinter hedge
      (critical_colorable_proper_induce h S hsproper)
      (critical_colorable_proper_induce h T htproper))

theorem critical_original_twoConnected [Fintype V] (hk : 2 ≤ k)
    (h : IsCriticalPlus k G) : TaskH.Fan.TwoConnected G := by
  have hc := critical_card_gt h
  exact ⟨by omega, critical_original_connected h, fun z => critical_deleted_connected hk h z⟩

#print axioms critical_original_connected
#print axioms critical_deleted_connected
#print axioms critical_original_twoConnected
end TaskH.General
