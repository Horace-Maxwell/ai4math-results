import Research.Backfill.Paper3.Proof.A.Consequences

/-!
# Paper 3, Lemma 3 (assembled) and Remark 4

Remark 4 (i): in a triangle-free `d`-regular graph on `2d` vertices, for an edge `uv` the
neighbourhoods `N(v)`, `N(u)` are disjoint independent `d`-sets covering `V`, and every vertex of
`N(v)` has neighbourhood `N(u)`; this gives an explicit isomorphism with `K_{d,d}`.
(ii) follows from (i), Proposition 2 and Lemma 3. (iii): `T(3K₄) = 12` and `Q(3K₄) = 3` are
checked by `decide +kernel`; the two counts follow from Proposition 2.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

/-- **Lemma 3.** -/
theorem lemma3 : Lemma3 := by
  intro V _ _ G _ d hG
  refine ⟨fun hd => Qcount_eq_zero_of_five_le G hd, fun hd => ?_, fun hd => ?_, fun hd => ?_,
    fun hd => ?_⟩
  · subst hd
    exact five_mul_Qcount_le G hG
  · subst hd
    exact two_mul_Qcount_le G hG
  · subst hd
    exact Qcount_eq_c4 G hG
  · have := five_mul_Qcount_le_of_three_le G hd hG
    omega

theorem kdd_cliqueFree (d : ℕ) : (Kdd d).CliqueFree 3 := by
  refine cliqueFree_three_of_coloring _ (fun x => x.isLeft) ?_
  rintro (x | x) (y | y) h <;> simp_all

/-- Remark 4 (i): a triangle-free `d`-regular graph on `2d` vertices is `K_{d,d}`. -/
theorem iso_kdd_of_triangleFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d) (hV : Fintype.card V = 2 * d)
    (hG : G.IsRegularOfDegree d) (hcf : G.CliqueFree 3) : Nonempty (G ≃g Kdd d) := by
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]
    omega
  obtain ⟨u⟩ := hne
  have hdeg : 0 < #(G.neighborFinset u) := by
    rw [card_neighborFinset_eq_degree, hG.degree_eq]
    omega
  obtain ⟨v, hv⟩ := card_pos.1 hdeg
  rw [mem_neighborFinset] at hv
  have hind : ∀ z x y, G.Adj z x → G.Adj z y → ¬ G.Adj x y := fun z x y hzx hzy hxy =>
    hcf {z, x, y} (is3Clique_triple_iff.2 ⟨hzx, hzy, hxy⟩)
  have hdisj : Disjoint (G.neighborFinset v) (G.neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [mem_neighborFinset] at hwA hwB
    exact hind u v w hv hwB hwA
  have hcardA : #(G.neighborFinset v) = d := by
    rw [card_neighborFinset_eq_degree, hG.degree_eq]
  have hcardB : #(G.neighborFinset u) = d := by
    rw [card_neighborFinset_eq_degree, hG.degree_eq]
  have hunion : G.neighborFinset v ∪ G.neighborFinset u = univ :=
    eq_univ_of_card _ (by rw [card_union_of_disjoint hdisj, hcardA, hcardB, hV]; ring)
  have hmem : ∀ x, x ∈ G.neighborFinset v ∨ x ∈ G.neighborFinset u := fun x =>
    mem_union.1 (hunion ▸ mem_univ x)
  have hNA : ∀ x ∈ G.neighborFinset v, G.neighborFinset x = G.neighborFinset u := by
    intro x hx
    apply eq_of_subset_of_card_le
    · intro y hy
      rcases hmem y with hyA | hyB
      · rw [mem_neighborFinset] at hx hy hyA
        exact absurd hy (hind v x y hx hyA)
      · exact hyB
    · rw [hcardB, card_neighborFinset_eq_degree, hG.degree_eq]
  have hadj : ∀ x y, G.Adj x y ↔ (x ∈ G.neighborFinset v ↔ y ∉ G.neighborFinset v) := by
    intro x y
    by_cases hx : x ∈ G.neighborFinset v <;> by_cases hy : y ∈ G.neighborFinset v
    · have : ¬ G.Adj x y := by
        rw [mem_neighborFinset] at hx hy
        exact hind v x y hx hy
      simp [hx, hy, this]
    · have hyB : y ∈ G.neighborFinset u := (hmem y).resolve_left hy
      rw [← hNA x hx, mem_neighborFinset] at hyB
      simp [hx, hy, hyB]
    · have hxB : x ∈ G.neighborFinset u := (hmem x).resolve_left hx
      rw [← hNA y hy, mem_neighborFinset] at hxB
      simp [hx, hy, hxB.symm]
    · have hxB : x ∈ G.neighborFinset u := (hmem x).resolve_left hx
      have hyB : y ∈ G.neighborFinset u := (hmem y).resolve_left hy
      have : ¬ G.Adj x y := by
        rw [mem_neighborFinset] at hxB hyB
        exact hind u x y hxB hyB
      simp [hx, hy, this]
  let eA : G.neighborFinset v ≃ Fin d :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcardA)
  let eB : G.neighborFinset u ≃ Fin d :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcardB)
  let g : V → Fin d ⊕ Fin d := fun x =>
    if hx : x ∈ G.neighborFinset v then .inl (eA ⟨x, hx⟩)
    else .inr (eB ⟨x, (hmem x).resolve_left hx⟩)
  have hinj : Function.Injective g := by
    intro x y hxy
    by_cases hx : x ∈ G.neighborFinset v <;> by_cases hy : y ∈ G.neighborFinset v <;>
      simp only [g, hx, hy, dite_true, dite_false] at hxy
    · exact congrArg Subtype.val (eA.injective (Sum.inl_injective hxy))
    · exact absurd hxy Sum.inl_ne_inr
    · exact absurd hxy Sum.inr_ne_inl
    · exact congrArg Subtype.val (eB.injective (Sum.inr_injective hxy))
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hV, Fintype.card_sum, Fintype.card_fin]; ring⟩
  refine ⟨⟨Equiv.ofBijective g hbij, fun {x y} => ?_⟩⟩
  show (Kdd d).Adj (g x) (g y) ↔ G.Adj x y
  rw [hadj]
  by_cases hx : x ∈ G.neighborFinset v <;> by_cases hy : y ∈ G.neighborFinset v <;>
    simp [g, hx, hy, -mem_neighborFinset]

/-- Remark 4 (ii). -/
theorem remark4_ii {d : ℕ} (hd : 3 ≤ d) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 2 * d)
    (hG : G.IsRegularOfDegree d) (hiso : IsEmpty (G ≃g Kdd d)) :
    iCount (Kdd d) (d ^ 2 - 3 * d + 1) < iCount G (d ^ 2 - 3 * d + 1) := by
  have hT : triangles G ≠ 0 := by
    intro h
    rw [triangles_eq_zero_iff] at h
    obtain ⟨φ⟩ := iso_kdd_of_triangleFree G (by omega) hV hG h
    exact hiso.false φ
  have ht : ((d ^ 2 - 3 * d + 1 : ℕ) : ℤ) = tStar (2 * d) d := by
    unfold tStar
    have h1 : d * (2 * d) / 2 = d * d := by
      rw [show d * (2 * d) = 2 * (d * d) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    have h3d : 3 * d ≤ d ^ 2 := by nlinarith
    rw [h1, Nat.cast_add, Nat.cast_sub h3d]
    push_cast
    ring
  rw [iCount_eq_NleZ, iCount_eq_NleZ, ht]
  have p1 := proposition2 V G d (by omega) hG
  rw [hV] at p1
  have p2 := proposition2 _ (Kdd d) d (by omega) (isRegularOfDegree_of_inst (kdd_regular d))
  have hcardK : Fintype.card (Fin d ⊕ Fin d) = 2 * d := by
    rw [Fintype.card_sum, Fintype.card_fin]
    ring
  rw [hcardK] at p2
  have hTK : triangles (Kdd d) = 0 := triangles_eq_zero (kdd_cliqueFree d)
  have hQK : Qcount (Kdd d) d = 0 := by
    have := five_mul_Qcount_le_of_three_le (Kdd d) hd (isRegularOfDegree_of_inst (kdd_regular d))
    rw [hTK] at this
    omega
  have hQG := five_mul_Qcount_le_of_three_le G hd hG
  have h1 : (1 : ℤ) ≤ triangles G := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hT
  have h2 : 5 * (Qcount G d : ℤ) ≤ 3 * triangles G := by exact_mod_cast hQG
  have : (NleZ (Kdd d) (tStar (2 * d) d) : ℤ) < NleZ G (tStar (2 * d) d) := by
    rw [p1, p2, hTK, hQK]
    push_cast
    linarith
  exact_mod_cast this

theorem top_regular (k : ℕ) [LocallyFinite (⊤ : SimpleGraph (Fin (k + 1)))] :
    (⊤ : SimpleGraph (Fin (k + 1))).IsRegularOfDegree k := by
  intro v
  rw [degree_eq_card_of_adj_iff _ _ (univ.erase v), card_erase_of_mem (mem_univ v), card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]
  intro w
  rw [top_adj, mem_erase]
  exact ⟨fun h => ⟨Ne.symm h, mem_univ w⟩, fun h => Ne.symm h.1⟩

set_option maxRecDepth 100000 in
theorem threeK4_triangles : triangles threeK4 = 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem threeK4_Qcount : Qcount threeK4 3 = 3 := by decide +kernel

theorem threeK4_iCount : iCount threeK4 10 = 4002 := by
  have p := proposition2 _ threeK4 3 (by norm_num)
    (isRegularOfDegree_of_inst (isRegularOfDegree_copies 3 (isRegularOfDegree_of_inst
      (top_regular 3))))
  have hc : Fintype.card (Fin 3 × Fin 4) = 12 := by simp
  have ht : tStar 12 3 = 10 := by decide
  have h66 : (12 : ℕ).choose 2 = 66 := by decide
  have h3 : (3 : ℕ).choose 2 = 3 := by decide
  rw [hc, ht, threeK4_triangles, threeK4_Qcount, h66, h3] at p
  rw [iCount_eq_NleZ]
  push_cast at p ⊢
  omega

theorem kddUnion23_iCount : iCount (KddUnion 2 3) 10 = 3981 := by
  have p := proposition2 _ (KddUnion 2 3) 3 (by norm_num)
    (isRegularOfDegree_of_inst (kddUnion_regular 2 3))
  have hc : Fintype.card (Fin 2 × (Fin 3 ⊕ Fin 3)) = 12 := by simp
  have ht : tStar 12 3 = 10 := by decide
  have h66 : (12 : ℕ).choose 2 = 66 := by decide
  have h3 : (3 : ℕ).choose 2 = 3 := by decide
  have hT : triangles (KddUnion 2 3) = 0 := triangles_eq_zero (kddUnion_cliqueFree 2 3)
  have hQ : Qcount (KddUnion 2 3) 3 = 0 := by
    have := two_mul_Qcount_le (KddUnion 2 3) (isRegularOfDegree_of_inst (kddUnion_regular 2 3))
    rw [hT] at this
    omega
  rw [hc, ht, hT, hQ, h66, h3] at p
  rw [iCount_eq_NleZ]
  push_cast at p ⊢
  omega

/-- **Remark 4.** -/
theorem remark4 : Remark4 := by
  refine ⟨fun d hd V _ _ G _ hV hG hcf => iso_kdd_of_triangleFree G hd hV hG hcf,
    fun d hd V _ _ G _ hV hG hiso => remark4_ii hd G hV hG hiso, by decide,
    by norm_num [gammaStar, tStar], threeK4_triangles, threeK4_Qcount, threeK4_iCount,
    kddUnion23_iCount, ?_⟩
  rw [threeK4_iCount, kddUnion23_iCount]
  norm_num

end P3A
