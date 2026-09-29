import Research.Backfill.Paper3.Challenge
import Research.Backfill.Paper3.Proof.Basic

/-!
# Paper 3, Theorem A cluster: basic tools

Edge counts `e_G(A)` of vertex sets: the insertion formula `e(A ∪ {v}) = e(A) + |N(v) ∩ A|`, the
handshake identity inside `A`, the bounds `e(A) ≤ C(|A|, 2)` (equality exactly for cliques) and
`2 e(A) ≤ d |A|` for `d`-regular graphs, explicit values on 2- and 3-sets; `i_γ` and `N_{≤t}` at
integer thresholds, their invariance under isomorphism for every real `γ`; degrees in `⊕g`,
`copies` and `K_{d,d}`; triangle-freeness of graphs with a proper 2-colouring.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
  rw [Nat.choose_one_right] at h
  omega

section EdgeCount

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `e(A ∪ {v}) = e(A) + |N(v) ∩ A|` for `v ∉ A`. -/
theorem edgesIn_insert {v : V} {A : Finset V} (hv : v ∉ A) :
    edgesIn G (insert v A) = edgesIn G A + #(A.filter (G.Adj v)) := by
  unfold edgesIn
  have hsplit : G.edgeFinset.filter (· ∈ (insert v A).sym2) =
      G.edgeFinset.filter (· ∈ A.sym2) ∪ (A.filter (G.Adj v)).image (fun w => s(v, w)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_filter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff, mem_insert,
        mem_union, mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨hxy, hx, hy⟩
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact absurd rfl hxy.ne
          · exact Or.inr ⟨y, ⟨hy, hxy⟩, Or.inl ⟨rfl, rfl⟩⟩
        · rcases hy with rfl | hy
          · exact Or.inr ⟨x, ⟨hx, hxy.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
          · exact Or.inl ⟨hxy, hx, hy⟩
      · rintro (⟨hxy, hx, hy⟩ | ⟨w, ⟨hw, hvw⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
        · exact ⟨hxy, Or.inr hx, Or.inr hy⟩
        · exact ⟨hvw, Or.inl rfl, Or.inr hw⟩
        · exact ⟨hvw.symm, Or.inr hw, Or.inl rfl⟩
  rw [hsplit, card_union_of_disjoint, card_image_of_injective]
  · intro w w' h
    exact Sym2.congr_right.1 h
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, -, rfl⟩ := mem_image.1 he'
    rw [mem_filter, Finset.mk_mem_sym2_iff] at he
    exact hv he.2.1

omit [Fintype V] in
theorem card_filter_insert_adj {v w : V} {A : Finset V} (hw : w ∉ A) :
    #((insert w A).filter (G.Adj v)) = #(A.filter (G.Adj v)) + if G.Adj v w then 1 else 0 := by
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hw (mem_filter.1 h').1)]
  · rw [add_zero]

/-- Handshake inside `A`: `2 e(A) = ∑_{v ∈ A} |N(v) ∩ A|`. -/
theorem two_mul_edgesIn_eq_sum (A : Finset V) :
    2 * edgesIn G A = ∑ v ∈ A, #(A.filter (G.Adj v)) := by
  induction A using Finset.induction_on with
  | empty => simp [edgesIn]
  | insert v A hv ih =>
    have h1 : (insert v A).filter (G.Adj v) = A.filter (G.Adj v) := by
      rw [filter_insert, ite_eq_right G.irrefl]
    have h2 : ∑ w ∈ A, #((insert v A).filter (G.Adj w)) =
        ∑ w ∈ A, #(A.filter (G.Adj w)) + #(A.filter (G.Adj v)) := by
      rw [card_filter (G.Adj v), ← sum_add_distrib]
      refine sum_congr rfl fun w _ => ?_
      rw [card_filter_insert_adj G hv]
      simp only [G.adj_comm w v]
    rw [edgesIn_insert G hv, sum_insert hv, h1, h2, ← ih]
    ring

theorem edgesIn_le_choose (A : Finset V) : edgesIn G A ≤ (#A).choose 2 := by
  induction A using Finset.induction_on with
  | empty => simp [edgesIn]
  | insert v A hv ih =>
    rw [edgesIn_insert G hv, card_insert_of_notMem hv, choose_two_succ]
    have := card_filter_le A (G.Adj v)
    omega

@[simp] theorem edgesIn_singleton (a : V) : edgesIn G {a} = 0 := by
  have := edgesIn_le_choose G {a}
  simpa using this

theorem edgesIn_mono {A B : Finset V} (h : A ⊆ B) : edgesIn G A ≤ edgesIn G B := by
  unfold edgesIn
  apply card_le_card
  intro e he
  rw [mem_filter] at he ⊢
  exact ⟨he.1, Finset.sym2_mono h he.2⟩

/-- In a `d`-regular graph, `2 e(A) ≤ d |A|`. -/
theorem two_mul_edgesIn_le {d : ℕ} (hG : G.IsRegularOfDegree d) (A : Finset V) :
    2 * edgesIn G A ≤ d * #A := by
  rw [two_mul_edgesIn_eq_sum]
  calc ∑ v ∈ A, #(A.filter (G.Adj v)) ≤ ∑ _v ∈ A, d := by
        refine sum_le_sum fun v _ => ?_
        rw [← hG.degree_eq v, ← card_neighborFinset_eq_degree]
        apply card_le_card
        intro w hw
        rw [mem_neighborFinset]
        exact (mem_filter.1 hw).2
    _ = d * #A := by rw [sum_const, smul_eq_mul, mul_comm]

/-- A set spanning `C(|A|, 2)` edges is a clique. -/
theorem isClique_of_choose_le {A : Finset V} (h : (#A).choose 2 ≤ edgesIn G A) :
    G.IsClique (A : Set V) := by
  intro a ha b hb hab
  have ha' : a ∈ A := ha
  have hb' : b ∈ A := hb
  have hA : insert a (A.erase a) = A := insert_erase ha'
  have hcard : #(A.erase a) + 1 = #A := card_erase_add_one ha'
  have key := edgesIn_insert G (notMem_erase a A)
  rw [hA] at key
  have hle := edgesIn_le_choose G (A.erase a)
  have hsub : (A.erase a).filter (G.Adj a) ⊆ A.erase a := filter_subset _ _
  have hc : #(A.erase a) ≤ #((A.erase a).filter (G.Adj a)) := by
    rw [← hcard, choose_two_succ] at h
    omega
  have heq := eq_of_subset_of_card_le hsub hc
  have hb'' : b ∈ A.erase a := mem_erase.2 ⟨fun h => hab h.symm, hb'⟩
  rw [← heq] at hb''
  exact (mem_filter.1 hb'').2

/-- A clique `A` spans exactly `C(|A|, 2)` edges. -/
theorem edgesIn_eq_choose_of_isClique {A : Finset V} (h : G.IsClique (A : Set V)) :
    edgesIn G A = (#A).choose 2 := by
  induction A using Finset.induction_on with
  | empty => simp [edgesIn]
  | insert v A hv ih =>
    rw [coe_insert, isClique_insert] at h
    rw [edgesIn_insert G hv, ih h.1, card_insert_of_notMem hv, choose_two_succ]
    congr 1
    rw [filter_true_of_mem]
    intro w hw
    exact h.2 w hw (by rintro rfl; exact hv hw)

theorem isClique_iff_choose_le {A : Finset V} :
    G.IsClique (A : Set V) ↔ (#A).choose 2 ≤ edgesIn G A :=
  ⟨fun h => (edgesIn_eq_choose_of_isClique G h).ge, isClique_of_choose_le G⟩

omit [Fintype V] in
theorem card_filter_pair (p : V → Prop) [DecidablePred p] {b c : V} (hbc : b ≠ c) :
    #(({b, c} : Finset V).filter p) = (if p b then 1 else 0) + if p c then 1 else 0 := by
  rw [card_filter, sum_pair hbc]

theorem edgesIn_pair {a b : V} (hab : a ≠ b) :
    edgesIn G {a, b} = if G.Adj a b then 1 else 0 := by
  have ha : a ∉ ({b} : Finset V) := by simpa using hab
  rw [edgesIn_insert G ha, edgesIn_singleton, card_filter, sum_singleton, zero_add]

theorem edgesIn_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    edgesIn G {a, b, c} = (if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) +
      (if G.Adj b c then 1 else 0) := by
  have ha : a ∉ ({b, c} : Finset V) := by simp [hab, hac]
  rw [edgesIn_insert G ha, edgesIn_pair G hbc, card_filter_pair _ hbc]
  ring

omit [DecidableEq V] in
/-- The number of `k`-subsets of `V`. -/
theorem card_filter_card_eq (k : ℕ) :
    #((univ : Finset (Finset V)).filter (fun S => #S = k)) = (Fintype.card V).choose k := by
  rw [univ_filter_card_eq, card_powersetCard, card_univ]

/-- `N_{≤t}` with a natural threshold is `NleZ` at the same integer. -/
theorem iCount_eq_NleZ (t : ℕ) : iCount G t = NleZ G t := by
  unfold iCount NleZ
  congr 1
  apply filter_congr
  intro A _
  exact Nat.cast_le.symm

/-- If `γ d n` is an integer `t`, then `i_γ = NleZ` at `t`. -/
theorem iGamma_eq_NleZ (d : ℕ) {γ : ℝ} (t : ℤ) (h : γ * d * (Fintype.card V : ℝ) = t) :
    iGamma G d γ = NleZ G t := by
  unfold iGamma NleZ
  congr 1
  apply filter_congr
  intro A _
  rw [h]
  norm_cast

end EdgeCount

section Iso

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Counting sets by a property of their edge count is invariant under isomorphism. -/
theorem card_filter_edgesIn_iso (e : G ≃g H) (p : ℕ → Prop) [DecidablePred p] :
    #((univ : Finset (Finset V)).filter (fun A => p (edgesIn G A))) =
      #((univ : Finset (Finset W)).filter (fun B => p (edgesIn H B))) := by
  apply Finset.card_bij (fun A _ => A.map e.toEquiv.toEmbedding)
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA ⊢
    rwa [P3Basic.edgesIn_map_iso]
  · intro A _ B _ h
    exact map_injective _ h
  · intro B hB
    refine ⟨B.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hB ⊢
      rwa [P3Basic.edgesIn_map_iso e.symm]
    · rw [Finset.map_map]
      conv_rhs => rw [← Finset.map_refl (s := B)]
      congr 1
      ext x
      exact e.apply_symm_apply x

/-- `i_γ` is invariant under isomorphism, for every real `γ`. -/
theorem iGamma_iso_all (e : G ≃g H) (d : ℕ) (γ : ℝ) : iGamma G d γ = iGamma H d γ := by
  classical
  unfold iGamma
  rw [Fintype.card_congr e.toEquiv]
  convert card_filter_edgesIn_iso e (fun n : ℕ => (n : ℝ) ≤ γ * d * (Fintype.card W : ℝ))

theorem NleZ_iso (e : G ≃g H) (t : ℤ) : NleZ G t = NleZ H t := by
  unfold NleZ
  exact card_filter_edgesIn_iso e (fun n : ℕ => (n : ℤ) ≤ t)

end Iso

section Degrees

variable {V W : Type*}

/-- Regularity does not depend on the `LocallyFinite` instance. -/
theorem isRegularOfDegree_of_inst {G : SimpleGraph V} {i1 i2 : LocallyFinite G} {d : ℕ}
    (h : @IsRegularOfDegree V G i1 d) : @IsRegularOfDegree V G i2 d := by
  intro v
  convert h v

/-- Degree from an explicit neighbour set (any `Fintype` instance on the neighbour set). -/
theorem degree_eq_card_of_adj_iff (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)]
    (s : Finset V) (h : ∀ w, G.Adj v w ↔ w ∈ s) : G.degree v = #s := by
  rw [← card_neighborSet_eq_degree, ← Set.toFinset_card]
  congr 1
  ext w
  simp [h]

theorem degree_sum_inl [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) [Fintype (G.neighborSet v)] [Fintype ((G ⊕g H).neighborSet (.inl v))] :
    (G ⊕g H).degree (.inl v) = G.degree v := by
  rw [degree_eq_card_of_adj_iff _ _ ((G.neighborFinset v).map Function.Embedding.inl),
    card_map, card_neighborFinset_eq_degree]
  intro w
  cases w <;> simp

theorem degree_sum_inr [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (w : W) [Fintype (H.neighborSet w)] [Fintype ((G ⊕g H).neighborSet (.inr w))] :
    (G ⊕g H).degree (.inr w) = H.degree w := by
  rw [degree_eq_card_of_adj_iff _ _ ((H.neighborFinset w).map Function.Embedding.inr),
    card_map, card_neighborFinset_eq_degree]
  intro x
  cases x <;> simp

theorem isRegularOfDegree_sum [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} [LocallyFinite G] [LocallyFinite H] [LocallyFinite (G ⊕g H)] {d : ℕ}
    (hG : G.IsRegularOfDegree d) (hH : H.IsRegularOfDegree d) : (G ⊕g H).IsRegularOfDegree d := by
  rintro (v | w)
  · rw [degree_sum_inl, hG.degree_eq]
  · rw [degree_sum_inr, hH.degree_eq]

theorem degree_copies (m : ℕ) [DecidableEq W] (G : SimpleGraph W) (x : Fin m × W)
    [Fintype (G.neighborSet x.2)] [Fintype ((copies m G).neighborSet x)] :
    (copies m G).degree x = G.degree x.2 := by
  rw [degree_eq_card_of_adj_iff _ _
    ((G.neighborFinset x.2).map ⟨fun y => (x.1, y), fun _ _ h => (Prod.ext_iff.1 h).2⟩),
    card_map, card_neighborFinset_eq_degree]
  intro y
  simp only [boxProd_adj, bot_adj, false_and, false_or, mem_map, mem_neighborFinset]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨y.2, h, Prod.ext h' rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, rfl⟩

theorem isRegularOfDegree_copies (m : ℕ) [DecidableEq W] {G : SimpleGraph W} [LocallyFinite G]
    [LocallyFinite (copies m G)] {d : ℕ} (hG : G.IsRegularOfDegree d) :
    (copies m G).IsRegularOfDegree d := by
  intro x
  rw [degree_copies, hG.degree_eq]

theorem kdd_regular (d : ℕ) [LocallyFinite (Kdd d)] : (Kdd d).IsRegularOfDegree d := by
  rintro (a | b)
  · rw [degree_eq_card_of_adj_iff _ _ ((univ : Finset (Fin d)).map Function.Embedding.inr),
      card_map, card_univ, Fintype.card_fin]
    intro w
    cases w <;> simp
  · rw [degree_eq_card_of_adj_iff _ _ ((univ : Finset (Fin d)).map Function.Embedding.inl),
      card_map, card_univ, Fintype.card_fin]
    intro w
    cases w <;> simp

theorem kddUnion_regular (m d : ℕ) [LocallyFinite (KddUnion m d)] :
    (KddUnion m d).IsRegularOfDegree d := by
  have : LocallyFinite (Kdd d) := fun v => inferInstance
  exact isRegularOfDegree_copies m (kdd_regular d)

theorem card_kddUnion (m d : ℕ) : Fintype.card (Fin m × (Fin d ⊕ Fin d)) = m * (2 * d) := by
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  ring

end Degrees

section Triangles

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A graph with a proper 2-colouring has no triangle. -/
theorem cliqueFree_three_of_coloring (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) : G.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, e, hab, hae, hbe, rfl⟩ := ht
  have h1 := hc _ _ hab
  have h2 := hc _ _ hae
  have h3 := hc _ _ hbe
  revert h1 h2 h3
  generalize c a = x
  generalize c b = y
  generalize c e = z
  revert x y z
  decide

theorem kddUnion_cliqueFree (m d : ℕ) : (KddUnion m d).CliqueFree 3 := by
  refine cliqueFree_three_of_coloring _ (fun x => x.2.isLeft) ?_
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  simp only [boxProd_adj, bot_adj, false_and, false_or, completeBipartiteGraph_adj] at h
  rcases h with ⟨h, -⟩
  rcases x with x | x <;> rcases y with y | y <;> simp_all

theorem triangles_eq_zero {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    triangles G = 0 := by
  unfold triangles
  rw [cliqueFinset_eq_empty_iff.2 h, card_empty]

theorem triangles_eq_zero_iff {G : SimpleGraph V} [DecidableRel G.Adj] :
    triangles G = 0 ↔ G.CliqueFree 3 := by
  unfold triangles
  rw [card_eq_zero, cliqueFinset_eq_empty_iff]

end Triangles

end P3A
