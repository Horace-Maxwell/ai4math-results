import Research.Backfill.Paper3.Proof.A.Lemma3
import Research.Backfill.Paper3.Proof.A.Blocks

/-!
# Paper 3: 2-regular and 1-regular graphs (Lemma 3 for `d = 2`, trivial cases)

In a 2-regular graph a 4-set with four edges is closed under adjacency and induces `C₄ ≅ K_{2,2}`,
so it is the vertex set of a component (`supp_eq_heavy`). Hence `Q(G) = c₄(G)` (Lemma 3, `d = 2`),
`4 Q(G) ≤ n`, and `4 Q(G) = n` forces `G ≅ (n/4) K_{2,2}` (block isomorphism over the
components). Also `Q((n/4) K_{2,2}) = n/4`, and every 1-regular graph on `n` vertices is
`(n/2) K_{1,1}`.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

section TwoRegular

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem heavy5_two_eq_empty (hG : G.IsRegularOfDegree 2) : heavy5 G 2 = ∅ := by
  rw [filter_eq_empty_iff]
  rintro S - ⟨hS, he⟩
  have := two_mul_edgesIn_le G hG S
  rw [hS] at this
  omega

theorem Qcount_two (hG : G.IsRegularOfDegree 2) : Qcount G 2 = #(heavy4 G 2) := by
  rw [Qcount_eq, heavy5_two_eq_empty G hG, card_empty, add_zero]

/-- A 4-set with four edges in a 2-regular graph is closed under adjacency. -/
theorem closed_of_heavy (hG : G.IsRegularOfDegree 2) {S : Finset V} (hS : S ∈ heavy4 G 2) :
    ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
  rw [mem_filter] at hS
  obtain ⟨-, hS4, he⟩ := hS
  have hsum := two_mul_edgesIn_eq_sum G S
  have hle : ∀ v ∈ S, #(S.filter (G.Adj v)) ≤ 2 := fun v _ => by
    rw [← hG.degree_eq v, ← card_neighborFinset_eq_degree]
    exact card_le_card (fun w hw => by
      rw [mem_neighborFinset]
      exact (mem_filter.1 hw).2)
  have heq : ∀ v ∈ S, #(S.filter (G.Adj v)) = 2 := by
    intro v hv
    by_contra hne
    have hlt : #(S.filter (G.Adj v)) < 2 := lt_of_le_of_ne (hle v hv) hne
    have : ∑ w ∈ S, #(S.filter (G.Adj w)) < ∑ _w ∈ S, 2 := sum_lt_sum hle ⟨v, hv, hlt⟩
    rw [sum_const, hS4, smul_eq_mul] at this
    omega
  intro x hx y hxy
  have hsub : S.filter (G.Adj x) ⊆ G.neighborFinset x := fun w hw => by
    rw [mem_neighborFinset]
    exact (mem_filter.1 hw).2
  have heq' := eq_of_subset_of_card_le hsub
    (by rw [card_neighborFinset_eq_degree, hG.degree_eq, heq x hx])
  have hy : y ∈ G.neighborFinset x := by
    rw [mem_neighborFinset]
    exact hxy
  rw [← heq'] at hy
  exact (mem_filter.1 hy).1

theorem induce_heavy_iso (hG : G.IsRegularOfDegree 2) {S : Finset V} (hS : S ∈ heavy4 G 2) :
    Nonempty (G.induce (S : Set V) ≃g Kdd 2) := by
  classical
  have hclosed := closed_of_heavy G hG hS
  have hreg : (G.induce (S : Set V)).IsRegularOfDegree 2 :=
    induce_isRegularOfDegree_of_closed G (fun x hx y hxy => hclosed x hx y hxy) hG
  have hcard : Fintype.card (S : Set V) = 4 := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
    exact (mem_filter.1 hS).2.1
  exact nonempty_iso_kdd_two _ hcard hreg

/-- A heavy 4-set is the vertex set of the component of each of its vertices. -/
theorem supp_eq_heavy (hG : G.IsRegularOfDegree 2) {S : Finset V} (hS : S ∈ heavy4 G 2) {v : V}
    (hv : v ∈ S) : (G.connectedComponentMk v).supp = (S : Set V) := by
  apply Set.Subset.antisymm
  · exact supp_subset_of_closed G (fun x hx y hxy => closed_of_heavy G hG hS x hx y hxy) hv
  · intro w hw
    obtain ⟨φ⟩ := induce_heavy_iso G hG hS
    have hconn : (G.induce (S : Set V)).Connected := (Iso.connected_iff φ).2 kdd_two_connected
    have hr := (hconn.preconnected ⟨v, hv⟩ ⟨w, hw⟩).map (Embedding.induce (S : Set V)).toHom
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.sound hr).symm

theorem heavy_disjoint (hG : G.IsRegularOfDegree 2) {S S' : Finset V} (hS : S ∈ heavy4 G 2)
    (hS' : S' ∈ heavy4 G 2) (hne : S ≠ S') : Disjoint S S' := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  apply hne
  exact Finset.coe_inj.1 ((supp_eq_heavy G hG hS hv).symm.trans (supp_eq_heavy G hG hS' hv'))

theorem card_biUnion_heavy (hG : G.IsRegularOfDegree 2) :
    #((heavy4 G 2).biUnion id) = 4 * #(heavy4 G 2) := by
  rw [card_biUnion (t := id) (fun S hS S' hS' hne => heavy_disjoint G hG hS hS' hne),
    sum_congr rfl (fun S hS => (mem_filter.1 hS).2.1), sum_const, smul_eq_mul, mul_comm]

theorem four_mul_card_heavy4_le (hG : G.IsRegularOfDegree 2) :
    4 * #(heavy4 G 2) ≤ Fintype.card V := by
  rw [← card_biUnion_heavy G hG]
  exact card_le_univ _

theorem exists_heavy_of_eq (hG : G.IsRegularOfDegree 2)
    (h : 4 * #(heavy4 G 2) = Fintype.card V) (v : V) : ∃ S ∈ heavy4 G 2, v ∈ S := by
  have hU : (heavy4 G 2).biUnion id = univ :=
    eq_univ_of_card _ (by rw [card_biUnion_heavy G hG, h])
  have : v ∈ (heavy4 G 2).biUnion id := by
    rw [hU]
    exact mem_univ v
  rw [mem_biUnion] at this
  obtain ⟨S, hS, hvS⟩ := this
  exact ⟨S, hS, hvS⟩

/-- If the heavy 4-sets cover `V`, then `G ≅ (n/4) K_{2,2}`. -/
theorem iso_kddUnion_of_cover (hG : G.IsRegularOfDegree 2)
    (h : 4 * #(heavy4 G 2) = Fintype.card V) :
    Nonempty (G ≃g KddUnion (Fintype.card V / 4) 2) := by
  classical
  have hcomp : ∀ c : G.ConnectedComponent,
      Nonempty (G.induce {v | G.connectedComponentMk v = c} ≃g Kdd 2) := by
    intro c
    obtain ⟨v, hv⟩ := c.nonempty_supp
    rw [ConnectedComponent.mem_supp_iff] at hv
    subst hv
    obtain ⟨S, hS, hvS⟩ := exists_heavy_of_eq G hG h v
    have hsupp : {w | G.connectedComponentMk w = G.connectedComponentMk v} = (S : Set V) :=
      supp_eq_heavy G hG hS hvS
    rw [hsupp]
    exact induce_heavy_iso G hG hS
  let _ : Fintype G.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨ψ⟩ := nonempty_iso_copies_of_blocks G (Kdd 2) G.connectedComponentMk
    (fun _ _ h => ConnectedComponent.connectedComponentMk_eq_of_adj h) (fun c => (hcomp c).some)
  have hcard : Fintype.card V = Fintype.card G.ConnectedComponent * 4 := by
    rw [Fintype.card_congr ψ.toEquiv, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum,
      Fintype.card_fin]
  have hk : Fintype.card V / 4 = Fintype.card G.ConnectedComponent := by omega
  rw [hk]
  exact ⟨ψ⟩

/-- A 2-regular graph on `n` vertices not isomorphic to `(n/4) K_{2,2}` has `4 Q < n`. -/
theorem four_mul_Qcount_lt (hG : G.IsRegularOfDegree 2)
    (hiso : IsEmpty (G ≃g KddUnion (Fintype.card V / 4) 2)) : 4 * Qcount G 2 < Fintype.card V := by
  rw [Qcount_two G hG]
  rcases lt_or_eq_of_le (four_mul_card_heavy4_le G hG) with h | h
  · exact h
  · obtain ⟨ψ⟩ := iso_kddUnion_of_cover G hG h
    exact (hiso.false ψ).elim

/-- **Lemma 3, `d = 2`:** `Q(G) = c₄(G)`. -/
theorem Qcount_eq_c4 (hG : G.IsRegularOfDegree 2) : Qcount G 2 = c4 G := by
  classical
  rw [Qcount_two G hG, c4, ← Nat.card_eq_finsetCard]
  symm
  let f : {c : G.ConnectedComponent // Nonempty (G.induce c.supp ≃g cycleGraph 4)} →
      ↥(heavy4 G 2) := fun c => ⟨univ.filter (fun v => G.connectedComponentMk v = c.1), by
        obtain ⟨φ⟩ := c.2
        have hcard : #(univ.filter (fun v => G.connectedComponentMk v = c.1)) = 4 := by
          rw [← Fintype.card_subtype]
          convert (Fintype.card_congr φ.toEquiv).trans (Fintype.card_fin 4)
          all_goals exact (ConnectedComponent.mem_supp_iff _ _).symm
        have hclosed : ∀ x ∈ univ.filter (fun v => G.connectedComponentMk v = c.1), ∀ y,
            G.Adj x y → y ∈ univ.filter (fun v => G.connectedComponentMk v = c.1) := by
          intro x hx y hxy
          rw [mem_filter] at hx ⊢
          exact ⟨mem_univ y, supp_closed G c.1 x hx.2 y hxy⟩
        have he := two_mul_edgesIn_of_closed G hclosed hG
        rw [hcard] at he
        rw [mem_filter]
        exact ⟨mem_univ _, hcard, by omega⟩⟩
  have hinj : Function.Injective f := by
    intro c c' hcc'
    have hval := congrArg Subtype.val hcc'
    obtain ⟨v, hv⟩ := c.1.nonempty_supp
    have hv1 : v ∈ (f c).1 := by
      simp only [f, mem_filter, mem_univ, true_and]
      exact hv
    rw [hval] at hv1
    simp only [f, mem_filter, mem_univ, true_and] at hv1
    exact Subtype.ext (hv.symm.trans hv1)
  have hsurj : Function.Surjective f := by
    rintro ⟨S, hS⟩
    have hS4 : #S = 4 := (mem_filter.1 hS).2.1
    obtain ⟨v, hv⟩ : S.Nonempty := by
      rw [← card_pos, hS4]
      norm_num
    have hsupp := supp_eq_heavy G hG hS hv
    refine ⟨⟨G.connectedComponentMk v, ?_⟩, ?_⟩
    · rw [hsupp]
      obtain ⟨φ⟩ := induce_heavy_iso G hG hS
      exact ⟨φ.trans cycleFourIsoKdd.symm⟩
    · apply Subtype.ext
      ext w
      simp only [f, mem_filter, mem_univ, true_and]
      rw [← ConnectedComponent.mem_supp_iff, hsupp]
      rfl
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end TwoRegular

/-- `Q((n/4) K_{2,2}) = n/4`: the `m` copies are the heavy 4-sets. -/
theorem card_heavy4_kddUnion (m : ℕ) : #(heavy4 (KddUnion m 2) 2) = m := by
  have hle := four_mul_card_heavy4_le (KddUnion m 2) (isRegularOfDegree_of_inst (kddUnion_regular m 2))
  rw [card_kddUnion] at hle
  have hge : m ≤ #(heavy4 (KddUnion m 2) 2) := by
    have hsub : (univ : Finset (Fin m)).image
        (fun i => ({i} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2))) ⊆
          heavy4 (KddUnion m 2) 2 := by
      intro S hS
      rw [mem_image] at hS
      obtain ⟨i, -, rfl⟩ := hS
      have hcard : #(({i} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2))) = 4 := by simp
      have hclosed : ∀ x ∈ ({i} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2)), ∀ y,
          (KddUnion m 2).Adj x y → y ∈ ({i} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2)) := by
        intro x hx y hxy
        simp only [mem_product, mem_singleton, mem_univ, and_true] at hx ⊢
        simp only [boxProd_adj, bot_adj, false_and, false_or] at hxy
        rw [← hxy.2, hx]
      have he := two_mul_edgesIn_of_closed (KddUnion m 2) hclosed
        (isRegularOfDegree_of_inst (kddUnion_regular m 2))
      rw [hcard] at he
      rw [mem_filter]
      exact ⟨mem_univ _, hcard, by omega⟩
    have := card_le_card hsub
    rw [card_image_of_injective] at this
    · simpa using this
    · intro i j hij
      have hij' : ({i} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2)) =
          ({j} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2)) := hij
      have : ((i, Sum.inl 0) : Fin m × (Fin 2 ⊕ Fin 2)) ∈
          ({j} : Finset (Fin m)) ×ˢ (univ : Finset (Fin 2 ⊕ Fin 2)) := by
        rw [← hij']
        simp
      simp only [mem_product, mem_singleton, mem_univ, and_true] at this
      exact this
  omega

section OneRegular

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every 1-regular graph on `n` vertices is `(n/2) K_{1,1}`. -/
theorem iso_kddUnion_one (hG : G.IsRegularOfDegree 1) :
    Nonempty (G ≃g KddUnion (Fintype.card V / 2) 1) := by
  classical
  have hcomp : ∀ c : G.ConnectedComponent,
      Nonempty (G.induce {v | G.connectedComponentMk v = c} ≃g Kdd 1) := by
    intro c
    obtain ⟨v, hv⟩ := c.nonempty_supp
    rw [ConnectedComponent.mem_supp_iff] at hv
    subst hv
    obtain ⟨w, hw⟩ := card_eq_one.1 (hG.degree_eq v : #(G.neighborFinset v) = 1)
    have hvw : G.Adj v w := by
      rw [← mem_neighborFinset, hw]
      exact mem_singleton_self w
    obtain ⟨u, hu⟩ := card_eq_one.1 (hG.degree_eq w : #(G.neighborFinset w) = 1)
    have hvu : v = u := by
      have : v ∈ G.neighborFinset w := by
        rw [mem_neighborFinset]
        exact hvw.symm
      rw [hu, mem_singleton] at this
      exact this
    have hclosed : ∀ x ∈ (({v, w} : Finset V) : Set V), ∀ y, G.Adj x y →
        y ∈ (({v, w} : Finset V) : Set V) := by
      intro x hx y hxy
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      have hy : y ∈ G.neighborFinset x := by
        rw [mem_neighborFinset]
        exact hxy
      rcases hx with rfl | rfl
      · rw [hw, mem_singleton] at hy
        exact Or.inr hy
      · rw [hu, mem_singleton] at hy
        exact Or.inl (hy.trans hvu.symm)
    have hsupp : {x | G.connectedComponentMk x = G.connectedComponentMk v} =
        (({v, w} : Finset V) : Set V) := by
      apply Set.Subset.antisymm (supp_subset_of_closed G hclosed (by simp))
      intro x hx
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
    rw [hsupp]
    have hreg : (G.induce (({v, w} : Finset V) : Set V)).IsRegularOfDegree 1 :=
      induce_isRegularOfDegree_of_closed G hclosed hG
    have hcard : Fintype.card (({v, w} : Finset V) : Set V) = 2 := by
      rw [← Set.toFinset_card, Finset.toFinset_coe, card_pair hvw.ne]
    exact nonempty_iso_kdd_one _ hcard hreg
  let _ : Fintype G.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨ψ⟩ := nonempty_iso_copies_of_blocks G (Kdd 1) G.connectedComponentMk
    (fun _ _ h => ConnectedComponent.connectedComponentMk_eq_of_adj h) (fun c => (hcomp c).some)
  have hcard : Fintype.card V = Fintype.card G.ConnectedComponent * 2 := by
    rw [Fintype.card_congr ψ.toEquiv, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum,
      Fintype.card_fin]
  have hk : Fintype.card V / 2 = Fintype.card G.ConnectedComponent := by omega
  rw [hk]
  exact ⟨ψ⟩

end OneRegular

end P3A
