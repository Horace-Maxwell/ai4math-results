import Research.TaskH.Gao.ActualSetCrossing

/-! The entry edge and positive tail belong to the original G and actual G-K component. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem actual_component_clique_entry [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x : V) (y : C.supp)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard) :
    ∃ u ∈ K, u ≠ x ∧ ∃ v : C.supp, G.Adj u v.1.1 := by
  classical
  obtain ⟨w, hwK, hwx⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < K.ncard) x
  have hyx : y.1.1 ≠ x := fun he => y.1.2 (he.symm ▸ hx)
  let S : Set {z : V // z ≠ x} := {z | ∃ v : C.supp, v.1.1 = z.1}
  have hyS : (⟨y.1.1, hyx⟩ : {z : V // z ≠ x}) ∈ S := ⟨y, rfl⟩
  have hwS : (⟨w, hwx⟩ : {z : V // z ≠ x}) ∉ S := by
    rintro ⟨v, he⟩
    exact v.1.2 (he.symm ▸ hwK)
  obtain ⟨a, ha, d, hd, e⟩ := reachable_crosses_vertex_set
    (G.induce {z : V | z ≠ x}) S ⟨y.1.1, hyx⟩ ⟨w, hwx⟩ hyS hwS
    ((hG.2.2 x) ⟨y.1.1, hyx⟩ ⟨w, hwx⟩)
  obtain ⟨v, hv⟩ := ha
  have hv' : v.1.1 = a.1 := hv
  have evG : G.Adj v.1.1 d.1 :=
    Eq.mpr (congrArg (fun z : V => G.Adj z d.1) hv') e
  have hdK : d.1 ∈ K := by
    by_contra hdK
    have evd : (G.induce Kᶜ).Adj v.1 ⟨d.1, hdK⟩ := evG
    have hdC := C.mem_supp_of_adj_mem_supp v.2 evd
    exact hd ⟨⟨⟨d.1, hdK⟩, hdC⟩, rfl⟩
  exact ⟨d.1, hdK, d.2, v, evG.symm⟩

theorem actual_component_clique_entry_tail [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x : V) (y : C.supp)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard) :
    ∃ u ∈ K, u ≠ x ∧ ∃ R : G.Walk u y.1.1,
      R.IsPath ∧ 1 ≤ R.length ∧ ∀ z ∈ R.support, z ∈ K → z = u := by
  obtain ⟨u, huK, hux, v, euv⟩ := actual_component_clique_entry G K C x y hG hx hK
  obtain ⟨p, hp⟩ := C.connected_toSimpleGraph.exists_isPath v y
  let f : C.toSimpleGraph →g G := {
    toFun := fun z => z.1.1
    map_rel' := fun e => e }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact Subtype.ext he
  let q : G.Walk v.1.1 y.1.1 := p.map f
  have hq : q.IsPath := (Walk.isPath_map_iff_of_injective hf).mpr hp
  have hqK : ∀ z ∈ q.support, z ∉ K := by
    intro z hz
    change z ∈ (p.map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨a, _ha, he⟩ := List.mem_map.mp hz
    have he' : a.1.1 = z := he
    exact he' ▸ a.1.2
  have huq : u ∉ q.support := fun hu => hqK u hu huK
  let R : G.Walk u y.1.1 := Walk.cons euv q
  refine ⟨u, huK, hux, R, hq.cons huq, ?_, ?_⟩
  · change 1 ≤ (Walk.cons euv q).length
    rw [Walk.length_cons]
    omega
  · intro z hz hzK
    change z ∈ (Walk.cons euv q).support at hz
    rw [Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact he
    · exact False.elim (hqK z hz hzK)

#print axioms actual_component_clique_entry
#print axioms actual_component_clique_entry_tail
end TaskH.Gao
