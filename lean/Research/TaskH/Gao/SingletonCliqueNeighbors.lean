import Research.TaskH.Fan.RootNeighborhood
import Research.TaskH.Fan.AdjEqConnectivity

/-! The actual singleton component forces the original neighbor set into K.
Deleting a simplicial vertex preserves connectivity by an explicit retraction.
The retraction transports reachability only, not prescribed path lengths. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_component_neighbors_subset [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) (hy : y ∉ K)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1) :
    G.neighborSet y ⊆ K := by
  let C := (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩
  let : Fintype C.supp := Fintype.ofFinite _
  have hsmallC : Fintype.card C.supp ≤ 1 := by
    change Nat.card C.supp ≤ 1 at hsmall
    simpa only [Nat.card_eq_fintype_card] using hsmall
  let : Subsingleton C.supp :=
    (Fintype.card_le_one_iff_subsingleton (α := C.supp)).mp hsmallC
  let yr : C.supp := ⟨⟨y, hy⟩, rfl⟩
  intro z eyz
  by_contra hz
  have eyzC : (G.induce Kᶜ).Adj
      (⟨y, hy⟩ : {v : V // v ∉ K}) ⟨z, hz⟩ := eyz
  have hzC : (⟨z, hz⟩ : {v : V // v ∉ K}) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp yr.2 eyzC
  let zr : C.supp := ⟨⟨z, hz⟩, hzC⟩
  have hzy : z = y := congrArg (fun t : C.supp => t.1.1) (Subsingleton.elim zr yr)
  exact eyz.ne hzy.symm

theorem singleton_component_neighbors_avoid_root [Fintype V] (G : SimpleGraph V)
    (K : Set V) (x y : V) (hy : y ∉ K) (hno : ¬G.Adj x y)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1) :
    G.neighborSet y ⊆ K \ {x} := by
  intro z ez
  refine ⟨singleton_component_neighbors_subset G K y hy hsmall ez, ?_⟩
  intro hz
  have hzx : z = x := hz
  exact hno (Eq.mp (congrArg (fun t : V => G.Adj t y) hzx) ez.symm)

theorem singleton_component_neighbors_clique [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) (hy : y ∉ K) (hK : G.IsClique K)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1) :
    G.IsClique (G.neighborSet y) := by
  intro a ha b hb hab
  exact hK (singleton_component_neighbors_subset G K y hy hsmall ha)
    (singleton_component_neighbors_subset G K y hy hsmall hb) hab

theorem twoConnected_neighbor_ncard_ge_two [Fintype V] (G : SimpleGraph V)
    (hG : TwoConnected G) (x y : V) (hxy : x ≠ y) :
    2 ≤ (G.neighborSet y).ncard := by
  obtain ⟨a, b, hab, ea, eb⟩ := twoConnected_two_root_neighbors G hG y x hxy.symm
  have hsub : ({a, b} : Set V) ⊆ G.neighborSet y := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · exact Eq.mp (congrArg (fun t : V => G.Adj y t) hz.symm) ea
    · have hzb : z = b := hz
      exact Eq.mp (congrArg (fun t : V => G.Adj y t) hzb.symm) eb
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hab] at hcard
  exact hcard

theorem connected_delete_of_neighbor_clique (G : SimpleGraph V) (y t : V)
    (hG : G.Connected) (ht : G.Adj y t)
    (hcl : G.IsClique (G.neighborSet y)) :
    (G.induce {v | v ≠ y}).Connected := by
  classical
  let r : V → {v : V // v ≠ y} := fun v =>
    if hv : v = y then ⟨t, ht.ne.symm⟩ else ⟨v, hv⟩
  have ry : r y = ⟨t, ht.ne.symm⟩ := by simp only [r, dite_eq_left rfl]
  have ro : ∀ v (hv : v ≠ y), r v = ⟨v, hv⟩ := by
    intro v hv
    simp only [r, dite_eq_right hv]
  have hs : Function.Surjective r := by
    intro v
    exact ⟨v.1, ro v.1 v.2⟩
  have he : ∀ {a b : V}, G.Adj a b → r a = r b ∨
      (G.induce {v | v ≠ y}).Adj (r a) (r b) := by
    intro a b e
    by_cases hay : a = y
    · subst a
      rw [ry, ro b e.ne.symm]
      by_cases htb : t = b
      · exact Or.inl (Subtype.ext htb)
      · exact Or.inr (hcl ht e htb)
    · by_cases hby : b = y
      · subst b
        rw [ro a e.ne, ry]
        by_cases hat : a = t
        · exact Or.inl (Subtype.ext hat)
        · exact Or.inr (hcl e.symm ht hat)
      · rw [ro a hay, ro b hby]
        exact Or.inr e
  exact connected_of_surjective_adj_or_eq r hs he hG

theorem twoConnected_delete_of_neighbor_clique [Fintype V] (G : SimpleGraph V)
    (y : V) [iY : Fintype {v : V // v ≠ y}] (hG : TwoConnected G)
    (hcard : 4 ≤ Fintype.card V) (hcl : G.IsClique (G.neighborSet y)) :
    @TwoConnected {v : V // v ≠ y} iY (G.induce {v : V | v ≠ y}) := by
  classical
  let : Fintype {v : V // v = y} := Fintype.ofFinite _
  have hc : Fintype.card {v : V // v ≠ y} = Fintype.card V - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun v : V => v = y))
  refine ⟨by omega, hG.2.2 y, ?_⟩
  intro z
  let Z : Set V := {v | v ≠ z.1}
  let yr : Z := ⟨y, z.2.symm⟩
  have hcz : (G.induce Z).IsClique ((G.induce Z).neighborSet yr) := by
    intro a ha b hb hab
    apply hcl ha hb
    intro he
    exact hab (Subtype.ext he)
  obtain ⟨a, b, hab, ea, eb⟩ :=
    twoConnected_two_root_neighbors G hG y z.1 z.2.symm
  have hex : ∃ t : Z, (G.induce Z).Adj yr t := by
    by_cases haz : a = z.1
    · have hbz : b ≠ z.1 := fun he => hab (haz.trans he.symm)
      exact ⟨⟨b, hbz⟩, eb⟩
    · exact ⟨⟨a, haz⟩, ea⟩
  obtain ⟨t, et⟩ := hex
  have hconn := connected_delete_of_neighbor_clique (G.induce Z) yr t
    (hG.2.2 z.1) et hcz
  let f : ((G.induce Z).induce {v | v ≠ yr}) →g
      ((G.induce {v | v ≠ y}).induce {v | v ≠ z}) := {
    toFun := fun q =>
      ⟨⟨q.1.1, by
          intro he
          exact q.2 (Subtype.ext he)⟩,
        by intro he; exact q.1.2 (congrArg Subtype.val he)⟩
    map_rel' := fun e => e }
  have hf : Function.Surjective f := by
    intro q
    refine ⟨⟨⟨q.1.1, ?_⟩, ?_⟩, ?_⟩
    · intro he
      exact q.2 (Subtype.ext he)
    · intro he
      exact q.1.2 (congrArg Subtype.val he)
    · exact Subtype.ext (Subtype.ext rfl)
  exact SimpleGraph.Connected.map f hf hconn

theorem singleton_component_delete_y_twoConnected [Fintype V] (G : SimpleGraph V)
    (K : Set V) (y : V) [iY : Fintype {v : V // v ≠ y}]
    (hG : TwoConnected G) (hy : y ∉ K) (hK : G.IsClique K)
    (hKcard : 3 ≤ K.ncard)
    (hsmall : Nat.card ((G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩).supp ≤ 1) :
    @TwoConnected {v : V // v ≠ y} iY (G.induce {v : V | v ≠ y}) := by
  have hproper : K ⊂ (Set.univ : Set V) := by
    refine ⟨Set.subset_univ K, ?_⟩
    intro h
    exact hy (h (Set.mem_univ y))
  have hlt := Set.ncard_lt_ncard hproper
  rw [Set.ncard_univ, ← Fintype.card_eq_nat_card] at hlt
  exact twoConnected_delete_of_neighbor_clique G y hG (by omega)
    (singleton_component_neighbors_clique G K y hy hK hsmall)

#print axioms singleton_component_neighbors_subset
#print axioms singleton_component_neighbors_avoid_root
#print axioms singleton_component_neighbors_clique
#print axioms twoConnected_neighbor_ncard_ge_two
#print axioms connected_delete_of_neighbor_clique
#print axioms twoConnected_delete_of_neighbor_clique
#print axioms singleton_component_delete_y_twoConnected
end TaskH.Gao
