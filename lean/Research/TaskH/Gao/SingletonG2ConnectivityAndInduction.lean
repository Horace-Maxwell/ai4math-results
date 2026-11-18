import Research.TaskH.Gao.SingletonG2Family
import Research.TaskH.Gao.SingletonCliqueNeighbors
import Research.TaskH.Gao.ActualCliqueComponentEntry
import Research.TaskH.Fan.RootedConnectivity

/-! Actual original components, not a supplied child-connectivity oracle, close G2. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_g2_other_component_away_y [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) (hy : y ∉ K)
    (C : (G.induce Kᶜ).ConnectedComponent)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (v : C.supp) : v.1.1 ≠ y := by
  intro he
  have he' : v.1 = (⟨y, hy⟩ : {z : V // z ∉ K}) := Subtype.ext he
  have hyC : (⟨y, hy⟩ : {z : V // z ∉ K}) ∈ C.supp :=
    Eq.mp (congrArg (fun z : {z : V // z ∉ K} => z ∈ C.supp) he') v.2
  exact hother hyC.symm

theorem singleton_g2_point_component_other [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) (hy : y ∉ K)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1)
    (z : V) (hzK : z ∉ K) (hzy : z ≠ y) :
    (G.induce Kᶜ).connectedComponentMk ⟨z, hzK⟩ ≠
      (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ := by
  intro he
  let C := (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩
  let : Fintype C.supp := Fintype.ofFinite _
  have hc : Fintype.card C.supp ≤ 1 := by
    change Nat.card C.supp ≤ 1 at hsmall
    simpa only [Fintype.card_eq_nat_card] using hsmall
  let : Subsingleton C.supp := (Fintype.card_le_one_iff_subsingleton (α := C.supp)).mp hc
  let zy : C.supp := ⟨⟨z, hzK⟩, he⟩
  let yy : C.supp := ⟨⟨y, hy⟩, rfl⟩
  exact hzy (congrArg (fun v : C.supp => v.1.1) (Subsingleton.elim zy yy))

theorem singleton_g2_core_attachment [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (hy : y ∉ K) (hx : x ∈ K)
    (hG : TwoConnected G) (hK : 2 ≤ K.ncard) (hno : ¬G.Adj x y)
    (C : (G.induce Kᶜ).ConnectedComponent)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
      D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
      (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
        ∃ d : D.supp, G.Adj x d.1.1) :
    ∃ a ∈ K, ¬G.Adj y a ∧ ∃ d : C.supp, G.Adj a d.1.1 := by
  classical
  by_cases ht : ∃ a, G.Adj y a ∧ ∃ d : C.supp, G.Adj a d.1.1
  · obtain ⟨d, ed⟩ := hG1 C hother ht
    exact ⟨x, hx, (fun e => hno e.symm), d, ed⟩
  · obtain ⟨z, hz⟩ := C.nonempty_supp
    obtain ⟨a, ha, _hax, d, ed⟩ := actual_component_clique_entry G K C x ⟨z, hz⟩ hG hx hK
    exact ⟨a, ha, (fun e => ht ⟨a, e, d, ed⟩), d, ed⟩

theorem singleton_g2_delete_neighbor_clique_connected [Fintype V]
    (G : SimpleGraph V) (K : Set V) (x y : V)
    (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K)
    (hcl : G.IsClique K) (hK : 3 ≤ K.ncard) (hno : ¬G.Adj x y)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1)
    (hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
      D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
      (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
        ∃ d : D.supp, G.Adj x d.1.1) :
    (G.induce {z | z ≠ y ∧ ¬G.Adj y z}).Connected := by
  classical
  let R : Set V := {z | z ≠ y ∧ ¬G.Adj y z}
  have hxy : x ≠ y := fun he => hy (Eq.mp (congrArg (fun v : V => v ∈ K) he) hx)
  let X : R := ⟨x, hxy, fun e => hno e.symm⟩
  have hYK := singleton_component_neighbors_subset G K y hy hsmall
  have hcore : ∀ (a : V) (haK : a ∈ K) (hay : a ≠ y) (haY : ¬G.Adj y a),
      (G.induce R).Reachable (⟨a, hay, haY⟩ : R) X := by
    intro a haK hay haY
    by_cases hax : a = x
    · have he : (⟨a, hay, haY⟩ : R) = X := Subtype.ext hax
      exact Eq.mpr (congrArg (fun v : R => (G.induce R).Reachable v X) he) Reachable.rfl
    · exact (show (G.induce R).Adj (⟨a, hay, haY⟩ : R) X from hcl haK hx hax).reachable
  have hto : ∀ z : R, (G.induce R).Reachable z X := by
    intro z
    by_cases hzK : z.1 ∈ K
    · exact hcore z.1 hzK z.2.1 z.2.2
    · let C := (G.induce Kᶜ).connectedComponentMk ⟨z.1, hzK⟩
      have hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ :=
        singleton_g2_point_component_other G K y hy hsmall z.1 hzK z.2.1
      obtain ⟨a, haK, haY, d, ead⟩ := singleton_g2_core_attachment G K x y hy hx
        hG (by omega) hno C hother hG1
      have hay : a ≠ y := fun he => hy (Eq.mp (congrArg (fun v : V => v ∈ K) he) haK)
      let f : C.toSimpleGraph →g G.induce R := {
        toFun := fun c => ⟨c.1.1,
          singleton_g2_other_component_away_y G K y hy C hother c,
          fun e => c.1.2 (hYK e)⟩
        map_rel' := fun e => e }
      let zr : C.supp := ⟨⟨z.1, hzK⟩, rfl⟩
      have hr : (G.induce R).Reachable (f zr) (f d) :=
        (C.connected_toSimpleGraph zr d).map f
      have hez : f zr = z := Subtype.ext rfl
      have eda : (G.induce R).Adj (f d) ⟨a, hay, haY⟩ := ead.symm
      exact Eq.mp (congrArg (fun v : R => (G.induce R).Reachable v X) hez)
        (hr.trans (eda.reachable.trans (hcore a haK hay haY)))
  exact { preconnected := fun a b => (hto a).trans (hto b).symm, nonempty := ⟨X⟩ }

theorem singleton_g2_delete_tag_connected [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K)
    (hcl : G.IsClique K) (hK : 3 ≤ K.ncard) (hno : ¬G.Adj x y)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1)
    (hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
      D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
      (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
        ∃ d : D.supp, G.Adj x d.1.1) :
    ((singletonG2Graph G y).induce {v | v ≠ none}).Connected := by
  let R : Set V := {z | z ≠ y ∧ ¬G.Adj y z}
  let f : G.induce R →g (singletonG2Graph G y).induce {v | v ≠ none} := {
    toFun := fun z => ⟨some ⟨⟨z.1, z.2.1⟩, z.2.2⟩, by intro he; cases he⟩
    map_rel' := fun e => e }
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | none => exact False.elim (hz rfl)
    | some z => exact ⟨⟨z.1.1, z.1.2, z.2⟩, Subtype.ext rfl⟩
  exact SimpleGraph.Connected.map f hf
    (singleton_g2_delete_neighbor_clique_connected G K x y hG hx hy hcl hK hno hsmall hG1)

theorem singleton_g2_twoConnected [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K)
    (hcl : G.IsClique K) (hK : 3 ≤ K.ncard) (hno : ¬G.Adj x y)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1)
    (hotherExists : ∃ C : (G.induce Kᶜ).ConnectedComponent,
      C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
      D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
      (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
        ∃ d : D.supp, G.Adj x d.1.1) :
    @TwoConnected (IdentificationVertex (singletonG2Collapse G y))
      (singletonG2Fintype G y) (singletonG2Graph G y) := by
  classical
  let : Fintype {z : V // z ≠ y} := Fintype.ofFinite _
  let : Fintype (IdentificationVertex (singletonG2Collapse G y)) := singletonG2Fintype G y
  have hxy : x ≠ y := fun he => hy (Eq.mp (congrArg (fun v : V => v ∈ K) he) hx)
  have hGy := singleton_component_delete_y_twoConnected G K y hG hy hcl hK hsmall
  have hm := twoConnected_neighbor_ncard_ge_two G hG x y hxy
  have hs : (singletonG2Collapse G y).Nonempty := by
    obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite (G.neighborSet y))).mp (by omega : 0 < (G.neighborSet y).ncard)
    exact ⟨⟨v, hv.ne.symm⟩, hv⟩
  obtain ⟨C, hother⟩ := hotherExists
  obtain ⟨z, hzC⟩ := C.nonempty_supp
  let dr : C.supp := ⟨z, hzC⟩
  have hdy := singleton_g2_other_component_away_y G K y hy C hother dr
  have hdY : ¬G.Adj y dr.1.1 := fun e => dr.1.2
    (singleton_component_neighbors_subset G K y hy hsmall e)
  let X := some (singletonG2Root G x y hxy hno)
  let Z : IdentificationVertex (singletonG2Collapse G y) := some ⟨⟨dr.1.1, hdy⟩, hdY⟩
  have hXZ : X ≠ Z := by
    intro he
    have he' : x = dr.1.1 := congrArg (fun q : {v : {a : V // a ≠ y} // v ∉ singletonG2Collapse G y} => q.1.1)
      (Option.some.inj he)
    exact dr.1.2 (Eq.mp (congrArg (fun v : V => v ∈ K) he') hx)
  have hXn : X ≠ none := by
    change (some (singletonG2Root G x y hxy hno) :
      IdentificationVertex (singletonG2Collapse G y)) ≠ none
    intro he
    cases he
  have hnZ : (none : IdentificationVertex (singletonG2Collapse G y)) ≠ Z := by
    change (none : IdentificationVertex (singletonG2Collapse G y)) ≠
      some ⟨⟨dr.1.1, hdy⟩, hdY⟩
    intro he
    cases he
  have hc : 2 < Fintype.card (IdentificationVertex (singletonG2Collapse G y)) :=
    Fintype.two_lt_card_iff.mpr ⟨X, none, Z, hXn, hXZ, hnZ⟩
  refine ⟨by omega, identification_connected (G.induce {v : V | v ≠ y})
    (singletonG2Collapse G y) hs hGy.2.1, ?_⟩
  intro z
  cases z with
  | none => exact singleton_g2_delete_tag_connected G K x y hG hx hy hcl hK hno hsmall hG1
  | some z =>
    exact identification_delete_retained_connected
      (G.induce {v : V | v ≠ y}) (singletonG2Collapse G y) hs z.1 z.2 (hGy.2.2 z.1)



theorem singleton_g2_other_component_exists [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (k : ℕ) (hy : y ∉ K)
    (hG : TwoConnected G) (hKk : K.ncard ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1) :
    ∃ C : (G.induce Kᶜ).ConnectedComponent,
      C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ := by
  classical
  by_contra hex
  have hall : ∀ z : V, z ∈ K ∨ z = y := by
    intro z
    by_cases hzK : z ∈ K
    · exact Or.inl hzK
    · by_cases hzy : z = y
      · exact Or.inr hzy
      · exact False.elim (hex ⟨(G.induce Kᶜ).connectedComponentMk ⟨z, hzK⟩,
          singleton_g2_point_component_other G K y hy hsmall z hzK hzy⟩)
  have hsub : (Set.univ : Set V) ⊆ K ∪ {y} := fun z _hz => hall z
  have hn := Set.ncard_le_ncard hsub
  rw [Set.ncard_univ, Set.union_singleton, Set.ncard_insert_of_notMem hy] at hn
  obtain ⟨z, hzx, hzy⟩ := exists_vertex_avoiding_two hG.1 x y
  have hdz := hd z hzx hzy
  have hlt := G.degree_lt_card_verts z
  rw [← G.ncard_neighborSet z, Fintype.card_eq_nat_card] at hlt
  omega

theorem singleton_g2_actual_branch [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K)
    (hcl : G.IsClique K) (hK : 3 ≤ K.ncard) (hKk : K.ncard ≤ k)
    (hno : ¬G.Adj x y) (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1)
    (hG1 : ∀ D : (G.induce Kᶜ).ConnectedComponent,
      D ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩ →
      (∃ a, G.Adj y a ∧ ∃ d : D.supp, G.Adj a d.1.1) →
        ∃ d : D.supp, G.Adj x d.1.1)
    (ih : ∀ (W : Type u) [_iW : Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Nat.card W < Nat.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let : Fintype (IdentificationVertex (singletonG2Collapse G y)) := singletonG2Fintype G y
  have hxy : x ≠ y := fun he => hy (Eq.mp (congrArg (fun v : V => v ∈ K) he) hx)
  let xr := some (singletonG2Root G x y hxy hno)
  let m := (G.neighborSet y).ncard
  have hm : 2 ≤ m := twoConnected_neighbor_ncard_ge_two G hG x y hxy
  have hmk : m ≤ k := le_trans
    (Set.ncard_le_ncard (singleton_component_neighbors_subset G K y hy hsmall)) hKk
  have hotherExists := singleton_g2_other_component_exists G K x y k hy hG hKk hd hsmall
  have htwo := singleton_g2_twoConnected G K x y hG hx hy hcl hK hno hsmall hotherExists hG1
  have hroot : RootedTwoConnected (singletonG2Graph G y) xr none := by
    constructor
    · change (some (singletonG2Root G x y hxy hno) :
        IdentificationVertex (singletonG2Collapse G y)) ≠ none
      intro he
      cases he
    · refine ⟨htwo.1, Connected.mono le_sup_left htwo.2.1, ?_⟩
      intro z
      have hz : (singletonG2Graph G y).induce {v | v ≠ z} ≤
          ((singletonG2Graph G y) ⊔ SimpleGraph.edge xr none).induce {v | v ≠ z} :=
        fun _ _ e => Or.inl e
      exact Connected.mono hz (htwo.2.2 z)
  have hdegree : NonrootDegreeAtLeast (singletonG2Graph G y) xr none (k - m + 1 + 1) := by
    have h := singleton_g2_nonroot_degree G x y hxy hno k (by omega) hmk hd
    simpa only [Nat.add_assoc] using h
  have hpaths := ih (IdentificationVertex (singletonG2Collapse G y))
    (singletonG2Graph G y) xr none (k - m + 1)
    (singleton_g2_strict_order G y (by omega)) (by omega) hroot hdegree
  have hfamily := singleton_g2_family_assembly G x y hxy hno
    (singleton_component_neighbors_clique G K y hy hcl hsmall)
    (k - m + 1) (by omega) (by omega) hpaths
  have hn : (k - m + 1) + (G.neighborSet y).ncard - 1 = k := by
    change k - m + 1 + m - 1 = k
    omega
  exact hn ▸ hfamily

#print axioms singleton_g2_other_component_away_y
#print axioms singleton_g2_point_component_other
#print axioms singleton_g2_core_attachment
#print axioms singleton_g2_delete_neighbor_clique_connected
#print axioms singleton_g2_delete_tag_connected
#print axioms singleton_g2_twoConnected
#print axioms singleton_g2_other_component_exists
#print axioms singleton_g2_actual_branch
end TaskH.Gao
