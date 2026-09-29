import Research.Backfill.Paper3.Proof.A.Prop2

/-!
# Paper 3, Lemma 3 for `d ≥ 3`

`Q(G)` counts the 4-sets with `≥ d + 2` edges (`heavy4`) and the 5-sets with `≥ 2d + 2` edges
(`heavy5`). For `d ≥ 5` both are empty (`e(S) ≤ C(|S|, 2)`). For `d = 4` they consist of copies of
`K₄` and `K₅`; double counting (triangle, `K₄`) and (`K₄`, `K₅`) incidences, with the bound on the
number of `(k+1)`-cliques containing a `k`-clique, gives `5Q ≤ 3T`. For `d = 3`, `heavy5` is
empty, every heavy 4-set contains two triangles and every triangle lies in at most one heavy
4-set, so `2Q ≤ T`.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The 4-sets with at least `d + 2` edges. -/
abbrev heavy4 (d : ℕ) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter (fun S => #S = 4 ∧ d + 2 ≤ edgesIn G S)

/-- The 5-sets with at least `2d + 2` edges. -/
abbrev heavy5 (d : ℕ) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter (fun S => #S = 5 ∧ 2 * d + 2 ≤ edgesIn G S)

theorem Qcount_eq (d : ℕ) : Qcount G d = #(heavy4 G d) + #(heavy5 G d) := rfl

theorem Qcount_eq_zero_of_five_le {d : ℕ} (hd : 5 ≤ d) : Qcount G d = 0 := by
  have h4 : heavy4 G d = ∅ := by
    rw [filter_eq_empty_iff]
    rintro S - ⟨hS, he⟩
    have := edgesIn_le_choose G S
    have h6 : (4 : ℕ).choose 2 = 6 := by decide
    rw [hS] at this
    omega
  have h5 : heavy5 G d = ∅ := by
    rw [filter_eq_empty_iff]
    rintro S - ⟨hS, he⟩
    have := edgesIn_le_choose G S
    have h10 : (5 : ℕ).choose 2 = 10 := by decide
    rw [hS] at this
    omega
  rw [Qcount_eq, h4, h5, card_empty]

theorem mem_cliqueFinset_of_choose_le {S : Finset V} {k : ℕ} (hS : #S = k)
    (he : k.choose 2 ≤ edgesIn G S) : S ∈ G.cliqueFinset k := by
  rw [mem_cliqueFinset_iff, isNClique_iff]
  exact ⟨isClique_of_choose_le G (by rw [hS]; exact he), hS⟩

theorem powersetCard_subset_cliqueFinset {K : Finset V} (hK : G.IsClique (K : Set V)) (j : ℕ) :
    powersetCard j K ⊆ G.cliqueFinset j := by
  intro t ht
  rw [mem_powersetCard] at ht
  rw [mem_cliqueFinset_iff, isNClique_iff]
  exact ⟨hK.subset (by exact_mod_cast ht.1), ht.2⟩

/-- A `k`-clique (`k ≥ 1`) of a `d`-regular graph lies in at most `d + 1 - k` cliques of size
`k + 1`. -/
theorem card_clique_supersets_le {d k : ℕ} (hG : G.IsRegularOfDegree d) {K : Finset V}
    (hK : G.IsNClique k K) (hk : 1 ≤ k) (F : Finset (Finset V))
    (hF : ∀ K' ∈ F, G.IsNClique (k + 1) K' ∧ K ⊆ K') : #F + k ≤ d + 1 := by
  obtain ⟨x, hx⟩ : K.Nonempty := by
    rw [← card_pos, hK.card_eq]
    omega
  have hsub : F ⊆ ((G.neighborFinset x) \ K).image (fun w => insert w K) := by
    intro K' hK'
    obtain ⟨hK'c, hKK'⟩ := hF K' hK'
    have hcard : #(K' \ K) = 1 := by
      have := card_sdiff_add_card_eq_card hKK'
      rw [hK'c.card_eq, hK.card_eq] at this
      omega
    obtain ⟨w, hw⟩ := card_eq_one.1 hcard
    have hw' : w ∈ K' \ K := by
      rw [hw]
      exact mem_singleton_self w
    obtain ⟨hwK', hwK⟩ := mem_sdiff.1 hw'
    rw [mem_image]
    refine ⟨w, mem_sdiff.2 ⟨?_, hwK⟩, ?_⟩
    · rw [mem_neighborFinset]
      exact hK'c.1 (hKK' hx) hwK' (fun h => hwK (h ▸ hx))
    · ext u
      constructor
      · intro hu
        rw [mem_insert] at hu
        rcases hu with rfl | hu
        · exact hwK'
        · exact hKK' hu
      · intro hu
        by_cases huK : u ∈ K
        · exact mem_insert_of_mem huK
        · have : u ∈ K' \ K := mem_sdiff.2 ⟨hu, huK⟩
          rw [hw, mem_singleton] at this
          rw [this]
          exact mem_insert_self w K
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := (G.neighborFinset x) \ K) (f := fun w => insert w K)
  have h3 := card_sdiff_add_card_inter (G.neighborFinset x) K
  have h4 : G.neighborFinset x ∩ K = K.erase x := by
    ext u
    rw [mem_inter, mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨hxu, huK⟩
      exact ⟨fun h => G.irrefl (h ▸ hxu), huK⟩
    · rintro ⟨hux, huK⟩
      exact ⟨hK.1 hx huK (Ne.symm hux), huK⟩
  rw [h4, card_erase_of_mem hx, hK.card_eq, card_neighborFinset_eq_degree, hG.degree_eq] at h3
  omega

/-- **Lemma 3, `d = 4`:** `5 Q ≤ 3 T`. -/
theorem five_mul_Qcount_le (hG : G.IsRegularOfDegree 4) : 5 * Qcount G 4 ≤ 3 * triangles G := by
  have hQ4 : #(heavy4 G 4) ≤ #(G.cliqueFinset 4) := by
    apply card_le_card
    intro S hS
    rw [mem_filter] at hS
    have h6 : (4 : ℕ).choose 2 = 6 := by decide
    exact mem_cliqueFinset_of_choose_le G hS.2.1 (by omega)
  have hQ5 : #(heavy5 G 4) ≤ #(G.cliqueFinset 5) := by
    apply card_le_card
    intro S hS
    rw [mem_filter] at hS
    have h10 : (5 : ℕ).choose 2 = 10 := by decide
    exact mem_cliqueFinset_of_choose_le G hS.2.1 (by omega)
  have hK4 : #(G.cliqueFinset 4) * 4 ≤ #(G.cliqueFinset 3) * 2 := by
    refine card_mul_le_card_mul (fun (K t : Finset V) => t ⊆ K) ?_ ?_
    · intro K hK
      rw [mem_cliqueFinset_iff] at hK
      have hsub : powersetCard 3 K ⊆
          (G.cliqueFinset 3).bipartiteAbove (fun (K t : Finset V) => t ⊆ K) K := by
        intro t ht
        rw [mem_bipartiteAbove]
        exact ⟨powersetCard_subset_cliqueFinset G hK.1 3 ht, (mem_powersetCard.1 ht).1⟩
      have := card_le_card hsub
      rw [card_powersetCard, hK.card_eq] at this
      simpa using this
    · intro t ht
      rw [mem_cliqueFinset_iff] at ht
      have := card_clique_supersets_le G hG ht (by norm_num)
        ((G.cliqueFinset 4).bipartiteBelow (fun (K t : Finset V) => t ⊆ K) t)
        (fun K' hK' => by
          rw [mem_bipartiteBelow, mem_cliqueFinset_iff] at hK'
          exact hK')
      omega
  have hK5 : #(G.cliqueFinset 5) * 5 ≤ #(G.cliqueFinset 4) * 1 := by
    refine card_mul_le_card_mul (fun (K t : Finset V) => t ⊆ K) ?_ ?_
    · intro K hK
      rw [mem_cliqueFinset_iff] at hK
      have hsub : powersetCard 4 K ⊆
          (G.cliqueFinset 4).bipartiteAbove (fun (K t : Finset V) => t ⊆ K) K := by
        intro t ht
        rw [mem_bipartiteAbove]
        exact ⟨powersetCard_subset_cliqueFinset G hK.1 4 ht, (mem_powersetCard.1 ht).1⟩
      have := card_le_card hsub
      rw [card_powersetCard, hK.card_eq] at this
      simpa using this
    · intro t ht
      rw [mem_cliqueFinset_iff] at ht
      have := card_clique_supersets_le G hG ht (by norm_num)
        ((G.cliqueFinset 5).bipartiteBelow (fun (K t : Finset V) => t ⊆ K) t)
        (fun K' hK' => by
          rw [mem_bipartiteBelow, mem_cliqueFinset_iff] at hK'
          exact hK')
      omega
  rw [Qcount_eq]
  unfold triangles
  omega

omit [Fintype V] in
theorem card_filter_triple (p : V → Prop) [DecidablePred p] {b c e : V} (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e) :
    #(({b, c, e} : Finset V).filter p) =
      (if p b then 1 else 0) + (if p c then 1 else 0) + (if p e then 1 else 0) := by
  rw [card_filter, sum_insert (by simp [hbc, hbe]), sum_pair hce]
  ring

theorem two_le_card_of_ne {α : Type*} {s : Finset α} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 2 ≤ #s := by
  classical
  have h := card_le_card (show ({x, y} : Finset α) ⊆ s by
    intro z hz
    rw [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy)
  rwa [card_pair hxy] at h

theorem mem_triangles_filter {S : Finset V} {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : G.Adj y z) (hsub : ({x, y, z} : Finset V) ⊆ S) :
    ({x, y, z} : Finset V) ∈ (G.cliqueFinset 3).filter (· ⊆ S) := by
  rw [mem_filter, mem_cliqueFinset_iff, is3Clique_triple_iff]
  exact ⟨⟨hxy, hxz, hyz⟩, hsub⟩

/-- A 4-set spanning at least five edges contains at least two triangles. -/
theorem two_le_triangles_of_heavy {S : Finset V} (hS : #S = 4) (he : 5 ≤ edgesIn G S) :
    2 ≤ #((G.cliqueFinset 3).filter (· ⊆ S)) := by
  obtain ⟨a, t, hat, rfl, ht⟩ := card_eq_succ.1 hS
  obtain ⟨b, c, e, hbc, hbe, hce, rfl⟩ := card_eq_three.1 ht
  simp only [mem_insert, mem_singleton, not_or] at hat
  obtain ⟨hab, hac, hae⟩ := hat
  rw [edgesIn_insert G (by simp [hab, hac, hae]), edgesIn_triple G hbc hbe hce,
    card_filter_triple _ hbc hbe hce] at he
  have s1 : ({b, c, e} : Finset V) ⊆ {a, b, c, e} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    tauto
  have s2 : ({a, c, e} : Finset V) ⊆ {a, b, c, e} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    tauto
  have s3 : ({a, b, e} : Finset V) ⊆ {a, b, c, e} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    tauto
  have s4 : ({a, b, c} : Finset V) ⊆ {a, b, c, e} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    tauto
  have d12 : ({b, c, e} : Finset V) ≠ {a, c, e} := fun h => by
    have : a ∈ ({b, c, e} : Finset V) := by rw [h]; simp
    simp [hab, hac, hae] at this
  have d13 : ({b, c, e} : Finset V) ≠ {a, b, e} := fun h => by
    have : a ∈ ({b, c, e} : Finset V) := by rw [h]; simp
    simp [hab, hac, hae] at this
  have d14 : ({b, c, e} : Finset V) ≠ {a, b, c} := fun h => by
    have : a ∈ ({b, c, e} : Finset V) := by rw [h]; simp
    simp [hab, hac, hae] at this
  have d23 : ({a, c, e} : Finset V) ≠ {a, b, e} := fun h => by
    have : b ∈ ({a, c, e} : Finset V) := by rw [h]; simp
    simp [Ne.symm hab, hbc, hbe] at this
  have d24 : ({a, c, e} : Finset V) ≠ {a, b, c} := fun h => by
    have : b ∈ ({a, c, e} : Finset V) := by rw [h]; simp
    simp [Ne.symm hab, hbc, hbe] at this
  have d34 : ({a, b, e} : Finset V) ≠ {a, b, c} := fun h => by
    have : c ∈ ({a, b, e} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc, hce] at this
  split_ifs at he <;> first
    | omega
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj b c› ‹G.Adj b e› ‹G.Adj c e› s1)
        (mem_triangles_filter G ‹G.Adj a c› ‹G.Adj a e› ‹G.Adj c e› s2) d12
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj b c› ‹G.Adj b e› ‹G.Adj c e› s1)
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a e› ‹G.Adj b e› s3) d13
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj b c› ‹G.Adj b e› ‹G.Adj c e› s1)
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a c› ‹G.Adj b c› s4) d14
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj a c› ‹G.Adj a e› ‹G.Adj c e› s2)
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a e› ‹G.Adj b e› s3) d23
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj a c› ‹G.Adj a e› ‹G.Adj c e› s2)
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a c› ‹G.Adj b c› s4) d24
    | exact two_le_card_of_ne
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a e› ‹G.Adj b e› s3)
        (mem_triangles_filter G ‹G.Adj a b› ‹G.Adj a c› ‹G.Adj b c› s4) d34

/-- In a cubic graph a triangle lies in at most one 4-set spanning five or more edges. -/
theorem card_heavy_supersets_le_one (hG : G.IsRegularOfDegree 3) {t : Finset V}
    (ht : G.IsNClique 3 t) : #((heavy4 G 3).filter (fun S => t ⊆ S)) ≤ 1 := by
  have key : ∀ S : Finset V, #S = 4 → 5 ≤ edgesIn G S → t ⊆ S →
      ∃ w, w ∉ t ∧ S = insert w t ∧ 2 ≤ #(t.filter (G.Adj w)) := by
    intro S hS4 hS5 htS
    have hcard : #(S \ t) = 1 := by
      have := card_sdiff_add_card_eq_card htS
      rw [hS4, ht.card_eq] at this
      omega
    obtain ⟨w, hw⟩ := card_eq_one.1 hcard
    have hw' : w ∈ S \ t := by
      rw [hw]
      exact mem_singleton_self w
    obtain ⟨hwS, hwt⟩ := mem_sdiff.1 hw'
    have hSeq : S = insert w t := by
      ext u
      constructor
      · intro hu
        by_cases hut : u ∈ t
        · exact mem_insert_of_mem hut
        · have : u ∈ S \ t := mem_sdiff.2 ⟨hu, hut⟩
          rw [hw, mem_singleton] at this
          rw [this]
          exact mem_insert_self w t
      · intro hu
        rw [mem_insert] at hu
        rcases hu with rfl | hu
        · exact hwS
        · exact htS hu
    refine ⟨w, hwt, hSeq, ?_⟩
    have := edgesIn_insert G hwt
    rw [← hSeq, edgesIn_eq_choose_of_isClique G ht.1, ht.card_eq] at this
    norm_num at this
    omega
  rw [card_le_one]
  intro S hS S' hS'
  simp only [mem_filter, mem_univ, true_and] at hS hS'
  obtain ⟨w, hwt, rfl, hw2⟩ := key S hS.1.1 (by omega) hS.2
  obtain ⟨w', hw't, rfl, hw'2⟩ := key S' hS'.1.1 (by omega) hS'.2
  by_contra hne
  have hww' : w ≠ w' := fun h => hne (by rw [h])
  have hinter : 1 ≤ #(t.filter (G.Adj w) ∩ t.filter (G.Adj w')) := by
    have h1 := card_union_add_card_inter (t.filter (G.Adj w)) (t.filter (G.Adj w'))
    have h2 : #(t.filter (G.Adj w) ∪ t.filter (G.Adj w')) ≤ #t :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [ht.card_eq] at h2
    omega
  obtain ⟨u, hu⟩ := card_pos.1 hinter
  rw [mem_inter, mem_filter, mem_filter] at hu
  obtain ⟨⟨hut, hwu⟩, -, hw'u⟩ := hu
  have hsub : insert w (insert w' (t.erase u)) ⊆ G.neighborFinset u := by
    intro z hz
    rw [mem_neighborFinset]
    simp only [mem_insert, mem_erase] at hz
    rcases hz with rfl | rfl | ⟨hzu, hzt⟩
    · exact hwu.symm
    · exact hw'u.symm
    · exact ht.1 hut hzt (Ne.symm hzu)
  have hw'n : w' ∉ t.erase u := fun h => hw't (mem_of_mem_erase h)
  have hwn : w ∉ insert w' (t.erase u) := by
    rw [mem_insert]
    rintro (h | h)
    · exact hww' h
    · exact hwt (mem_of_mem_erase h)
  have hcard : #(insert w (insert w' (t.erase u))) = 4 := by
    rw [card_insert_of_notMem hwn, card_insert_of_notMem hw'n, card_erase_of_mem hut,
      ht.card_eq]
  have := card_le_card hsub
  rw [hcard, card_neighborFinset_eq_degree, hG.degree_eq] at this
  omega

/-- **Lemma 3, `d = 3`:** `2 Q ≤ T`. -/
theorem two_mul_Qcount_le (hG : G.IsRegularOfDegree 3) : 2 * Qcount G 3 ≤ triangles G := by
  have h5 : heavy5 G 3 = ∅ := by
    rw [filter_eq_empty_iff]
    rintro S - ⟨hS, he⟩
    have := two_mul_edgesIn_le G hG S
    rw [hS] at this
    omega
  have h4 : #(heavy4 G 3) * 2 ≤ #(G.cliqueFinset 3) * 1 := by
    refine card_mul_le_card_mul (fun (S t : Finset V) => t ⊆ S) ?_ ?_
    · intro S hS
      rw [mem_filter] at hS
      exact two_le_triangles_of_heavy G hS.2.1 (by omega)
    · intro t ht
      exact card_heavy_supersets_le_one G hG (mem_cliqueFinset_iff.1 ht)
  rw [Qcount_eq, h5, card_empty]
  unfold triangles
  omega

/-- Lemma 3, last assertion: for `d ≥ 3`, `7 T ≤ 5 (2T - Q)`, i.e. `5 Q ≤ 3 T`. -/
theorem five_mul_Qcount_le_of_three_le {d : ℕ} (hd : 3 ≤ d) (hG : G.IsRegularOfDegree d) :
    5 * Qcount G d ≤ 3 * triangles G := by
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with rfl | rfl | h
  · have := two_mul_Qcount_le G hG
    omega
  · exact five_mul_Qcount_le G hG
  · rw [Qcount_eq_zero_of_five_le G h]
    omega

end P3A
