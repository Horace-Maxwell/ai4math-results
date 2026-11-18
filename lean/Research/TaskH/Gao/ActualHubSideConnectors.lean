import Research.TaskH.Gao.MaximalRegionActualAttachments
import Research.TaskH.Gao.TerminalFragmentCarrierRoute

/-! Real outside-component sides supply the two hub connectors, including
an empty exit connector when the actual hub is the terminal y block.
This local side lemma is not the missing incidence-route qualification. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem actual_carrier_component_torso_connected (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S) (hG : G.Connected)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    (G.induce (componentRegion C Set.univ ∪ {(carrierAttachment G S hS C).1})).Connected := by
  classical
  let a := carrierAttachment G S hS C
  let T := componentRegion C Set.univ ∪ {a.1}
  apply TaskH.Fan.rootedSet_connected G T a.1 (Or.inr rfl) _ hG
  intro z hz hza d ezd
  rcases hz with ⟨zr, _hzr, he⟩ | he
  · have e : G.Adj (componentVertex C zr) d :=
      Eq.mpr (congrArg (fun z : V => G.Adj z d) he) ezd
    by_cases hdS : d ∈ S
    · exact Or.inr (congrArg Subtype.val (carrierAttachment_unique G S hS C zr ⟨d, hdS⟩ e))
    · let dr : C.supp := ⟨⟨d, hdS⟩, C.mem_supp_of_adj_mem_supp zr.2 e⟩
      exact Or.inl ⟨dr, Set.mem_univ dr, rfl⟩
  · exact False.elim (hza he)

theorem actual_hub_sides_produce_connectors [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (u v : S) (huv : u ≠ v)
    (I : Set V) (b y : V) (hI : TerminalFragment G I b)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hCu : carrierAttachment G S hS C = u)
    (hIC : I ⊆ componentRegion C Set.univ)
    (hySide : y = v.1 ∨ ∃ D : (G.induce Sᶜ).ConnectedComponent,
      carrierAttachment G S hS D = v ∧ y ∈ componentRegion D Set.univ) :
    ∃ (T U : Set V), Disjoint T U ∧ fragmentBlock I b ⊆ T ∧
      (∀ z ∈ T, z ∈ S → z = u.1) ∧ (∀ z ∈ U, z ∈ S → z = v.1) ∧
      ∃ (Z0 : G.Walk b u.1) (Z1 : G.Walk v.1 y), Z0.IsPath ∧ Z1.IsPath ∧
        (∀ z ∈ Z0.support, z ∈ T ∧ z ∉ I) ∧
        (∀ z ∈ Z1.support, z ∈ U) ∧
        (∀ z ∈ Z0.support, z ∈ fragmentBlock I b → z = b) := by
  classical
  let T := componentRegion C Set.univ ∪ {u.1}
  have hT : (G.induce T).Connected := by
    have hh := actual_carrier_component_torso_connected G S hS hG C
    rw [hCu] at hh
    exact hh
  have hIT : I ⊆ T := fun z hz => Or.inl (hIC hz)
  have huI : u.1 ∉ I := fun h => Set.disjoint_left.mp
    (componentRegion_disjoint C Set.univ) (hIC h) u.2
  obtain ⟨hbT, Z0, hZ0, hZ0T, hZ0B⟩ :=
    terminal_boundary_route_in_connected_carrier G T I b u.1 hT hIT (Or.inr rfl) huI hI
  have hBT : fragmentBlock I b ⊆ T := by
    rintro z (he | hzI)
    · exact Eq.mpr (congrArg (fun z : V => z ∈ T) he) hbT
    · exact hIT hzI
  have hTS : ∀ z ∈ T, z ∈ S → z = u.1 := by
    rintro z (hzC | he) hzS
    · exact False.elim (Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) hzC hzS)
    · exact he
  rcases hySide with hy | ⟨D, hDv, hyD⟩
  · subst y
    let U : Set V := {v.1}
    have hTU : Disjoint T U := by
      apply Set.disjoint_left.mpr
      intro z hzT hzU
      have hzv : z = v.1 := hzU
      have hzu := hTS z hzT (Eq.mpr (congrArg (fun z : V => z ∈ S) hzv) v.2)
      exact huv (Subtype.ext (hzu.symm.trans hzv))
    refine ⟨T, U, hTU, hBT, hTS, ?_, Z0, Walk.nil, hZ0, Walk.IsPath.nil, hZ0T, ?_, hZ0B⟩
    · intro z hzU _hzS; exact hzU
    · intro z hz
      exact (show z = v.1 from by simpa only [Walk.support_nil, List.mem_singleton] using hz)
  · let U := componentRegion D Set.univ ∪ {v.1}
    have hCD : C ≠ D := by
      intro he
      have huEq : u = v := hCu.symm.trans ((congrArg (carrierAttachment G S hS) he).trans hDv)
      exact huv huEq
    have hRegions : Disjoint (componentRegion C Set.univ) (componentRegion D Set.univ) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨p, _hp, he⟩ ⟨q, _hq, heq⟩
      have hpq : p.1 = q.1 := Subtype.ext (he.trans heq.symm)
      have hqC : q.1 ∈ C.supp := Eq.mp
        (congrArg (fun z : {z : V // z ∉ S} => z ∈ C.supp) hpq) p.2
      exact hCD (ConnectedComponent.eq_of_common_vertex hqC q.2)
    have hTU : Disjoint T U := by
      apply Set.disjoint_left.mpr
      rintro z (hzC | heU) (hzD | heV)
      · exact Set.disjoint_left.mp hRegions hzC hzD
      · exact Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) hzC
          (Eq.mpr (congrArg (fun z : V => z ∈ S) heV) v.2)
      · exact Set.disjoint_left.mp (componentRegion_disjoint D Set.univ) hzD
          (Eq.mpr (congrArg (fun z : V => z ∈ S) heU) u.2)
      · exact huv (Subtype.ext (heU.symm.trans heV))
    have hU : (G.induce U).Connected := by
      have hh := actual_carrier_component_torso_connected G S hS hG D
      rw [hDv] at hh
      exact hh
    obtain ⟨p, hp⟩ := hU.exists_isPath ⟨v.1, Or.inr rfl⟩ ⟨y, Or.inl hyD⟩
    let f : G.induce U →g G := (Embedding.induce U).toHom
    let Z1 : G.Walk v.1 y := p.map f
    have hZ1 : Z1.IsPath := (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hp
    have hZ1U : ∀ z ∈ Z1.support, z ∈ U := by
      intro z hz
      change z ∈ (p.map f).support at hz
      rw [Walk.support_map] at hz
      obtain ⟨r, _hr, he⟩ := List.mem_map.mp hz
      have he' : r.1 = z := he
      exact Eq.mp (congrArg (fun z : V => z ∈ U) he') r.2
    refine ⟨T, U, hTU, hBT, hTS, ?_, Z0, Z1, hZ0, hZ1, hZ0T, hZ1U, hZ0B⟩
    rintro z (hzD | he) hzS
    · exact False.elim (Set.disjoint_left.mp (componentRegion_disjoint D Set.univ) hzD hzS)
    · exact he

#print axioms actual_carrier_component_torso_connected
#print axioms actual_hub_sides_produce_connectors
end TaskH.Gao
