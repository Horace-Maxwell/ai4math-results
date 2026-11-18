import Research.TaskH.Gao.ActualCliqueComponentEntry
import Research.TaskH.Gao.CliqueBoundaryBudget
import Research.TaskH.Fan.BoundaryQuotientConnectivity

/-! Independent actual G1 geometry; no SingletonCliqueNeighbors/Nat.card-le-one dependency. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def singletonG1Boundary (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) : Set V :=
  {a | a ∈ K ∧ ∃ d : C.supp, G.Adj d.1.1 a}

theorem singleton_g1_full_neighbor_cover (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (d : C.supp) (z : V)
    (e : G.Adj d.1.1 z) :
    z ∈ K ∨ ∃ hz : z ∉ K, (⟨z, hz⟩ : {v : V // v ∉ K}) ∈ C.supp := by
  classical
  by_cases hz : z ∈ K
  · exact Or.inl hz
  · have e' : (G.induce Kᶜ).Adj d.1 (⟨z, hz⟩ : {v : V // v ∉ K}) := e
    exact Or.inr ⟨hz, C.mem_supp_of_adj_mem_supp d.2 e'⟩

theorem singleton_g1_two_boundary_points [Fintype V] (G : SimpleGraph V)
    (K : Set V) (C : (G.induce Kᶜ).ConnectedComponent) (x : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard) :
    ∃ a ∈ singletonG1Boundary G K C, ∃ b ∈ singletonG1Boundary G K C, a ≠ b := by
  obtain ⟨p, hp⟩ := C.nonempty_supp
  let pr : C.supp := ⟨p, hp⟩
  obtain ⟨a, ha, _hax, d, ead⟩ := actual_component_clique_entry G K C x pr hG hx hK
  obtain ⟨b, hb, hba, e, ebe⟩ := actual_component_clique_entry G K C a pr hG ha hK
  exact ⟨a, ⟨ha, d, ead.symm⟩, b, ⟨hb, e, ebe.symm⟩, hba.symm⟩

theorem singleton_g1_boundary_ncard_ge_two [Fintype V] (G : SimpleGraph V)
    (K : Set V) (C : (G.induce Kᶜ).ConnectedComponent) (x : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard) :
    2 ≤ (singletonG1Boundary G K C).ncard := by
  obtain ⟨a, ha, b, hb, hab⟩ := singleton_g1_two_boundary_points G K C x hG hx hK
  have hsub : ({a, b} : Set V) ⊆ singletonG1Boundary G K C := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact Eq.mpr (congrArg (fun v : V => v ∈ singletonG1Boundary G K C) he) ha
    · have he' : z = b := he
      exact Eq.mpr (congrArg (fun v : V => v ∈ singletonG1Boundary G K C) he') hb
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hab] at hc
  exact hc

theorem singleton_g1_boundary_away [Fintype V] (G : SimpleGraph V)
    (K : Set V) (C : (G.induce Kᶜ).ConnectedComponent) (x v : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard) :
    ∃ a ∈ singletonG1Boundary G K C, a ≠ v := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := singleton_g1_two_boundary_points G K C x hG hx hK
  by_cases hav : a = v
  · exact ⟨b, hb, fun hbv => hab (hav.trans hbv.symm)⟩
  · exact ⟨a, ha, hav⟩

theorem singleton_g1_point_ne_y (G : SimpleGraph V) (K : Set V)
    (y : V) (hy : y ∉ K) (C : (G.induce Kᶜ).ConnectedComponent)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩) (d : C.supp) :
    d.1.1 ≠ y := by
  intro he
  have he' : d.1 = (⟨y, hy⟩ : {v : V // v ∉ K}) := Subtype.ext he
  have hyC : (⟨y, hy⟩ : {v : V // v ∉ K}) ∈ C.supp :=
    Eq.mp (congrArg (fun v : {v : V // v ∉ K} => v ∈ C.supp) he') d.2
  exact hother hyC.symm

def singletonG1Vertices (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) : Set V :=
  {z | ∃ hz : z ∉ K, (⟨z, hz⟩ : {v : V // v ∉ K}) ∈ C.supp}

theorem singletonG1Vertices_ncard (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) :
    (singletonG1Vertices G K C).ncard = Nat.card C.supp := by
  have he : singletonG1Vertices G K C = Set.range (fun d : C.supp => d.1.1) := by
    ext z
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨⟨⟨z, hz⟩, hzC⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d.1.2, d.2⟩
  have hi : Function.Injective (fun d : C.supp => d.1.1) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  rw [he]
  exact Set.ncard_range_of_injective hi

theorem singleton_g1_native_strict_order [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) (hy : y ∉ K) (hK : 3 ≤ K.ncard)
    (C : (G.induce Kᶜ).ConnectedComponent)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩) :
    Nat.card C.supp + 2 < Nat.card V := by
  let R := singletonG1Vertices G K C
  have hyR : y ∉ R := by
    rintro ⟨hy', hyC⟩
    exact singleton_g1_point_ne_y G K y hy C hother ⟨⟨y, hy'⟩, hyC⟩ rfl
  have hdis : Disjoint (R ∪ {y}) K := by
    apply Set.disjoint_left.mpr
    intro z hz hzK
    rcases hz with hz | hz
    · obtain ⟨hzK', _hzC⟩ := hz
      exact hzK' hzK
    · have he : z = y := hz
      exact hy (Eq.mp (congrArg (fun t : V => t ∈ K) he) hzK)
  have hb := clique_core_strict_order_budget (R ∪ {y}) K hdis hK
  have he : (R ∪ {y}).ncard = R.ncard + 1 := by
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hyR]
  have hr : R.ncard = Nat.card C.supp := singletonG1Vertices_ncard G K C
  omega

theorem singleton_g1_native_boundary_budget [Fintype V] (G : SimpleGraph V)
    (K : Set V) (C : (G.induce Kᶜ).ConnectedComponent) (x v : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard)
    (hv : v ∈ singletonG1Boundary G K C)
    (hxD : ¬∃ d : C.supp, G.Adj x d.1.1) :
    (singletonG1Boundary G K C \ {v}).Nonempty ∧
      (singletonG1Boundary G K C \ {v}) ⊆ K \ {x, v} ∧
      (singletonG1Boundary G K C \ {v}).ncard + 2 ≤ K.ncard := by
  have hxB : x ∉ singletonG1Boundary G K C := by
    rintro ⟨_hxK, d, edx⟩
    exact hxD ⟨d, edx.symm⟩
  have hxv : x ≠ v := fun he => hxB
    (Eq.mpr (congrArg (fun z : V => z ∈ singletonG1Boundary G K C) he) hv)
  obtain ⟨a, ha, hav⟩ := singleton_g1_boundary_away G K C x v hG hx hK
  have hsub : (singletonG1Boundary G K C \ {v}) ⊆ K \ {x, v} := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    intro he
    rcases Set.mem_insert_iff.mp he with he | he
    · exact hxB (Eq.mp (congrArg (fun t : V => t ∈ singletonG1Boundary G K C) he) hz.1)
    · exact hz.2 he
  have hdis : Disjoint (singletonG1Boundary G K C \ {v}) ({x, v} : Set V) := by
    apply Set.disjoint_left.mpr
    intro z hz hp
    exact (hsub hz).2 hp
  have hun : (singletonG1Boundary G K C \ {v}) ∪ ({x, v} : Set V) ⊆ K := by
    intro z hz
    rcases hz with hz | hz
    · exact hz.1.1
    · rcases Set.mem_insert_iff.mp hz with he | he
      · exact Eq.mpr (congrArg (fun t : V => t ∈ K) he) hx
      · have he' : z = v := he
        exact Eq.mpr (congrArg (fun t : V => t ∈ K) he') hv.1
  have hc := Set.ncard_le_ncard hun
  rw [Set.ncard_union_eq hdis, Set.ncard_pair hxv] at hc
  exact ⟨⟨a, ha, hav⟩, hsub, hc⟩
theorem singleton_g1_full_boundary (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) :
    equalBranchBoundary G (singletonG1Vertices G K C) = singletonG1Boundary G K C := by
  ext a
  constructor
  · rintro ⟨haR, d, hdR, eda⟩
    obtain ⟨hdK, hdC⟩ := hdR
    let dr : C.supp := ⟨⟨d, hdK⟩, hdC⟩
    rcases singleton_g1_full_neighbor_cover G K C dr a eda with haK | haC
    · exact ⟨haK, dr, eda⟩
    · exact False.elim (haR haC)
  · rintro ⟨haK, d, eda⟩
    refine ⟨?_, d.1.1, ⟨d.1.2, d.2⟩, eda⟩
    rintro ⟨haK', _haC⟩
    exact haK' haK

theorem singleton_g1_interior_connected (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) :
    (G.induce (singletonG1Vertices G K C)).Connected := by
  let f : C.toSimpleGraph →g G.induce (singletonG1Vertices G K C) := {
    toFun := fun d => ⟨d.1.1, d.1.2, d.2⟩
    map_rel' := fun e => e }
  have hf : Function.Surjective f := by
    rintro ⟨d, hdK, hdC⟩
    exact ⟨⟨⟨d, hdK⟩, hdC⟩, Subtype.ext rfl⟩
  exact SimpleGraph.Connected.map f hf C.connected_toSimpleGraph

@[instance_reducible]
noncomputable def singletonG1Fintype [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (v : V) :
    Fintype (IdentificationVertex (boundaryCollapse G (singletonG1Vertices G K C) v)) :=
  Fintype.ofFinite _

def boundaryRetainedRegionEquiv (G : SimpleGraph V) (R : Set V) (v : V)
    (hv : v ∈ equalBranchBoundary G R) :
    {a : boundaryDomain G R // a ∉ boundaryCollapse G R v} ≃ (R ∪ {v} : Set V) where
  toFun a := ⟨a.1.1, by
    rcases a.1.2 with ha | ha
    · exact Or.inl ha
    · right
      by_contra hav
      exact a.2 ⟨ha, hav⟩⟩
  invFun a := ⟨⟨a.1, by
      rcases a.2 with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ equalBranchBoundary G R) ha) hv)⟩,
    by
      rintro ⟨haB, hav⟩
      rcases a.2 with haR | haV
      · exact haB.1 haR
      · exact hav haV⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv a := Subtype.ext rfl

theorem singleton_g1_order [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (v : V)
    (hv : v ∈ singletonG1Boundary G K C) :
    Nat.card (IdentificationVertex (boundaryCollapse G (singletonG1Vertices G K C) v)) =
      Nat.card C.supp + 2 := by
  classical
  let R := singletonG1Vertices G K C
  have hvB : v ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary G K C]
    exact hv
  let : Fintype {a : boundaryDomain G R // a ∉ boundaryCollapse G R v} := Fintype.ofFinite _
  have ho : Nat.card (IdentificationVertex (boundaryCollapse G R v)) =
      Nat.card {a : boundaryDomain G R // a ∉ boundaryCollapse G R v} + 1 := by
    simpa only [IdentificationVertex, Fintype.card_eq_nat_card] using
      (Fintype.card_option (α := {a : boundaryDomain G R // a ∉ boundaryCollapse G R v}))
  rw [ho, Nat.card_congr (boundaryRetainedRegionEquiv G R v hvB), Nat.card_coe_set_eq,
    Set.union_singleton, Set.ncard_insert_of_notMem hvB.1]
  have hr := singletonG1Vertices_ncard G K C
  change R.ncard = Nat.card C.supp at hr
  omega

theorem singleton_g1_rooted [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x v : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hK : 2 ≤ K.ncard)
    (hv : v ∈ singletonG1Boundary G K C) :
    @RootedTwoConnected (IdentificationVertex (boundaryCollapse G (singletonG1Vertices G K C) v))
      (singletonG1Fintype G K C v) (boundaryQuotient G (singletonG1Vertices G K C) v) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G K C) v
        (by rw [singleton_g1_full_boundary G K C]; exact hv))) := by
  classical
  let R := singletonG1Vertices G K C
  let : Fintype (IdentificationVertex (boundaryCollapse G R v)) := singletonG1Fintype G K C v
  have hvB : v ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary G K C]
    exact hv
  obtain ⟨a, ha, hav⟩ := singleton_g1_boundary_away G K C x v hG hx hK
  have haB : a ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary G K C]
    exact ha
  have hc : (boundaryCollapse G R v).Nonempty :=
    ⟨⟨a, Or.inr haB⟩, haB, hav⟩
  exact boundaryQuotient_rooted G R v hvB (singleton_g1_interior_connected G K C) hc hG

theorem singleton_g1_strict_order [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (y v : V)
    (hy : y ∉ K) (hK : 3 ≤ K.ncard)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hv : v ∈ singletonG1Boundary G K C) :
    Nat.card (IdentificationVertex (boundaryCollapse G (singletonG1Vertices G K C) v)) <
      Nat.card V := by
  rw [singleton_g1_order G K C v hv]
  exact singleton_g1_native_strict_order G K y hy hK C hother

#print axioms singletonG1Boundary
#print axioms singleton_g1_full_neighbor_cover
#print axioms singleton_g1_two_boundary_points
#print axioms singleton_g1_boundary_ncard_ge_two
#print axioms singleton_g1_boundary_away
#print axioms singleton_g1_point_ne_y
#print axioms singletonG1Vertices
#print axioms singletonG1Vertices_ncard
#print axioms singleton_g1_native_strict_order
#print axioms singleton_g1_native_boundary_budget
#print axioms singleton_g1_full_boundary
#print axioms singleton_g1_interior_connected
#print axioms singletonG1Fintype
#print axioms boundaryRetainedRegionEquiv
#print axioms singleton_g1_order
#print axioms singleton_g1_rooted
#print axioms singleton_g1_strict_order
end TaskH.Gao
