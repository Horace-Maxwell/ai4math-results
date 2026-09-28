import Mathlib

set_option autoImplicit false

/-!
# A negative answer to Question 1.3 of Carenini, arXiv:2609.28527v1

Carenini ("Counting almost independent sets in regular graphs", arXiv:2609.28527v1) sets, for a
`d`-regular graph `G` on `n` vertices and `γ ≥ 0`,
`i_γ(G) = |{A ⊆ V(G) : e_G(A) ≤ γ d n}|`, where `e_G(A)` is the number of edges of `G` with both
endpoints in `A`, and asks (Question 1.3):

> Suppose that `2d ∣ n`. For every `γ ≥ 0`, is `i_γ(G)` maximized, among `d`-regular graphs on
> `n` vertices, by the disjoint union of `n/(2d)` copies of `K_{d,d}`?

We formalise the question literally (`CareniniQuestion n d γ`, quantifying over all finite vertex
types of cardinality `n`, with a real `γ`) and prove that it fails:

* `not_careniniQuestion_six : ¬ CareniniQuestion 6 3 (1/18)`: the triangular prism `K_3 □ K_2`
  has 28 vertex sets spanning at most one edge, `K_{3,3}` has 24 (`γ d n = (1/18)·3·6 = 1`);
* `not_careniniQuestion_two_d : ∀ d ≥ 3, ¬ CareniniQuestion (2d) d (1/(2d²))`: the switched
  `K_{d,d}` (`K_{d,d} - {x₀y₀, x₁y₁} + {x₀x₁, y₀y₁}`) is `d`-regular and every set spanning at most
  one edge of `K_{d,d}` spans at most one edge of it, with `{x₀, y₀, y₂}` as an extra set;
* `not_careniniQuestion_eight_two : ¬ CareniniQuestion 8 2 (1/16)` (`C_8` vs `2 C_4`),
  `not_careniniQuestion_twelve_bip : ¬ CareniniQuestion 12 3 (1/36)` (a connected bipartite cubic
  graph `H_3` vs `2 K_{3,3}`: the answer is negative even among bipartite graphs, with two copies),
  `not_careniniQuestion_twelve_top : ¬ CareniniQuestion 12 3 (5/18)` (`3 K_4` vs `2 K_{3,3}`).

All finite counts are checked by `decide` / `decide +kernel` (kernel reduction); no `native_decide`.
-/

namespace Carenini

open Finset SimpleGraph

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `e_G(A)`: the number of edges of `G` with both endpoints in `A`. -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  #(G.edgeFinset.filter (· ∈ A.sym2))

/-- `#{A ⊆ V : e_G(A) ≤ t}` for a natural-number threshold `t`. -/
def iCount (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : ℕ :=
  #((univ : Finset (Finset V)).filter (fun A => edgesIn G A ≤ t))

open Classical in
/-- Carenini's `i_γ(G) = |{A ⊆ V(G) : e_G(A) ≤ γ d n}|` with a real parameter `γ`,
where `n = |V|` and `d` is the degree. -/
noncomputable def iGamma (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (γ : ℝ) : ℕ :=
  #((univ : Finset (Finset V)).filter
    (fun A => ((edgesIn G A : ℕ) : ℝ) ≤ γ * d * (Fintype.card V : ℝ)))

/-- For `γ ≥ 0`, the real threshold `γ d n` can be replaced by its floor. -/
theorem iGamma_eq_iCount_floor (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) : iGamma G d γ = iCount G ⌊γ * d * (Fintype.card V : ℝ)⌋₊ := by
  classical
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  have h0 : (0 : ℝ) ≤ γ * d * (Fintype.card V : ℝ) := by positivity
  exact (Nat.le_floor_iff h0).symm

/-- If `γ d n` is a natural number `t`, then `i_γ(G) = #{A : e_G(A) ≤ t}`. -/
theorem iGamma_eq_iCount (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {γ : ℝ} (t : ℕ)
    (h : γ * d * (Fintype.card V : ℝ) = t) : iGamma G d γ = iCount G t := by
  classical
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [h]
  exact Nat.cast_le

end Defs

/-- The disjoint union of `m` copies of `K_{d,d}`, on the vertex type `Fin m × (Fin d ⊕ Fin d)`:
`(i, x) ~ (j, y)` iff `i = j` and `x, y` lie on different sides. -/
def KddUnion (m d : ℕ) : SimpleGraph (Fin m × (Fin d ⊕ Fin d)) where
  Adj x y := x.1 = y.1 ∧ (completeBipartiteGraph (Fin d) (Fin d)).Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, (completeBipartiteGraph (Fin d) (Fin d)).symm.symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => (completeBipartiteGraph (Fin d) (Fin d)).loopless.irrefl _ h.2⟩

instance (d : ℕ) : DecidableRel (completeBipartiteGraph (Fin d) (Fin d)).Adj := fun x y =>
  inferInstanceAs
    (Decidable (x.isLeft = true ∧ y.isRight = true ∨ x.isRight = true ∧ y.isLeft = true))

instance (m d : ℕ) : DecidableRel (KddUnion m d).Adj := fun x y =>
  inferInstanceAs (Decidable (x.1 = y.1 ∧ (completeBipartiteGraph (Fin d) (Fin d)).Adj x.2 y.2))

/-- **Carenini's Question 1.3**, the claim for fixed `n`, `d` and `γ`: every `d`-regular graph on
`n` vertices (on any finite vertex type of cardinality `n`) has `i_γ` at most that of the disjoint
union of `n / (2d)` copies of `K_{d,d}`. The paper's standing hypothesis `2d ∣ n` is not built in;
every instance refuted below satisfies it (`6 = 2·3`, `2d = 2·d`, `8 = 2·2·2`, `12 = 2·2·3`). -/
def CareniniQuestion (n d : ℕ) (γ : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.IsRegularOfDegree d →
      iGamma G d γ ≤ iGamma (KddUnion (n / (2 * d)) d) d γ

/-! ## The two graphs on `Fin 6` -/

/-- `K_{3,3}` on `Fin 6`: sides `{0,1,2}` and `{3,4,5}`. -/
def K33 : SimpleGraph (Fin 6) where
  Adj i j := (i.val < 3 ∧ 3 ≤ j.val) ∨ (3 ≤ i.val ∧ j.val < 3)
  symm := ⟨fun i j h => by omega⟩
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel K33.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val < 3 ∧ 3 ≤ j.val) ∨ (3 ≤ i.val ∧ j.val < 3)))

/-- The triangular prism `K_3 □ K_2` on `Fin 6`: triangles `{0,1,2}` and `{3,4,5}` plus the
perfect matching `0–3, 1–4, 2–5`. -/
def prism : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ ((i.val < 3 ↔ j.val < 3) ∨ i.val % 3 = j.val % 3)
  symm := ⟨fun i j h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl h2.symm
    · exact Or.inr h2.symm⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance : DecidableRel prism.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i.val < 3 ↔ j.val < 3) ∨ i.val % 3 = j.val % 3)))

/-! ### Both graphs are 3-regular -/

theorem K33_regular : K33.IsRegularOfDegree 3 := by
  intro v; revert v; decide

theorem prism_regular : prism.IsRegularOfDegree 3 := by
  intro v; revert v; decide

/-! ### They are the standard graphs: `K33 ≅ K_{3,3}` and `prism ≅ K_3 □ K_2` -/

/-- `K33` is isomorphic to Mathlib's `completeBipartiteGraph (Fin 3) (Fin 3)`. -/
def K33Iso : K33 ≃g completeBipartiteGraph (Fin 3) (Fin 3) where
  toEquiv := (finSumFinEquiv (m := 3) (n := 3)).symm
  map_rel_iff' := by
    intro a b; revert a b; decide

instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G □ H).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1))

/-- `prism` is isomorphic to the box product `K_3 □ K_2` of complete graphs. -/
def prismIso : prism ≃g ((⊤ : SimpleGraph (Fin 3)) □ (⊤ : SimpleGraph (Fin 2))) where
  toEquiv :=
    { toFun := fun i => (⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨i.val / 3, by omega⟩)
      invFun := fun p => ⟨p.1.val + 3 * p.2.val, by omega⟩
      left_inv := by intro i; revert i; decide
      right_inv := by intro p; revert p; decide }
  map_rel_iff' := by
    intro a b; revert a b; decide

/-- `K33` is isomorphic to the reference graph of the question, one copy of `K_{3,3}`. -/
def K33IsoKddUnion : K33 ≃g KddUnion 1 3 where
  toEquiv := finSumFinEquiv.symm.trans (Equiv.punitProd (α := Fin 3 ⊕ Fin 3)).symm |>.trans
    (Equiv.prodCongr finOneEquiv.symm (Equiv.refl _))
  map_rel_iff' := by
    intro a b; revert a b; decide

/-! ### The counts -/

theorem iCount_K33_one : iCount K33 1 = 24 := by decide

theorem iCount_prism_one : iCount prism 1 = 28 := by decide

theorem iCount_KddUnion_one : iCount (KddUnion 1 3) 1 = 24 := by decide

/-- For completeness: at `γ = 0` (independent sets) `K_{3,3}` wins, `15 > 13`. -/
theorem iCount_zero : iCount K33 0 = 15 ∧ iCount prism 0 = 13 := by decide

/-- `γ d n = (1/18)·3·6 = 1`. -/
theorem threshold_six : (1 / 18 : ℝ) * (3 : ℕ) * (6 : ℕ) = ((1 : ℕ) : ℝ) := by norm_num

theorem iGamma_prism : iGamma prism 3 (1 / 18) = 28 := by
  rw [iGamma_eq_iCount prism 3 1 (by simpa using threshold_six)]
  exact iCount_prism_one

theorem iGamma_K33 : iGamma K33 3 (1 / 18) = 24 := by
  rw [iGamma_eq_iCount K33 3 1 (by simpa using threshold_six)]
  exact iCount_K33_one

theorem iGamma_KddUnion : iGamma (KddUnion (6 / (2 * 3)) 3) 3 (1 / 18) = 24 := by
  show iGamma (KddUnion 1 3) 3 (1 / 18) = 24
  rw [iGamma_eq_iCount (KddUnion 1 3) 3 1 (by simp; norm_num)]
  exact iCount_KddUnion_one

/-- **Main theorem.** The answer to Carenini's Question 1.3 is negative for
`(n, d, γ) = (6, 3, 1/18)`: the prism is `3`-regular on `6` vertices and
`i_{1/18}(prism) = 28 > 24 = i_{1/18}(K_{3,3})`. -/
theorem not_careniniQuestion_six : ¬ CareniniQuestion 6 3 (1 / 18) := by
  intro h
  have h1 := h (Fin 6) prism (by simp) prism_regular
  rw [iGamma_prism, iGamma_KddUnion] at h1
  omega

/-- The same statement in explicit form, with Mathlib's `K_{3,3}`. -/
theorem prism_beats_K33 :
    prism.IsRegularOfDegree 3 ∧ K33.IsRegularOfDegree 3 ∧
      iGamma K33 3 (1 / 18) < iGamma prism 3 (1 / 18) := by
  refine ⟨prism_regular, K33_regular, ?_⟩
  rw [iGamma_prism, iGamma_K33]
  norm_num

/-! ## General `d ≥ 3` at `n = 2d`: the switched `K_{d,d}` (Theorem B, qualitative form)

`S_d` is `K_{d,d}` on `Fin d ⊕ Fin d` with the cross edges `x₀y₀`, `x₁y₁` removed and the edges
`x₀x₁`, `y₀y₁` added (indices are the values `0, 1` in `Fin d`). We show:
every set spanning at most one edge of `K_{d,d}` spans at most one edge of `S_d`, and the set
`{x₀, y₀, y₂}` spans two edges of `K_{d,d}` but one edge of `S_d`. Hence
`i_1(S_d) > i_1(K_{d,d})`, and Question 1.3 fails at `(n, d, γ) = (2d, d, 1/(2d²))` for every
`d ≥ 3`. -/

section General

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- `e_G(A) ≤ 1` iff any two edges of `G` inside `A` coincide. -/
theorem edgesIn_le_one_iff (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    edgesIn G A ≤ 1 ↔ ∀ u ∈ A, ∀ v ∈ A, ∀ u' ∈ A, ∀ v' ∈ A,
      G.Adj u v → G.Adj u' v' → s(u, v) = s(u', v') := by
  unfold edgesIn
  rw [Finset.card_le_one]
  constructor
  · intro h u hu v hv u' hu' v' hv' huv hu'v'
    apply h
    · simp [Finset.mem_filter, SimpleGraph.mem_edgeFinset, hu, hv, huv]
    · simp [Finset.mem_filter, SimpleGraph.mem_edgeFinset, hu', hv', hu'v']
  · intro h e he e' he'
    induction e using Sym2.ind with
    | h u v =>
      induction e' using Sym2.ind with
      | h u' v' =>
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff] at he he'
        exact h u he.2.1 v he.2.2 u' he'.2.1 v' he'.2.2 he.1 he'.1

/-- `e_G(A)` is invariant under graph isomorphism. -/
theorem edgesIn_map_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (A : Finset V) :
    edgesIn H (A.map e.toEquiv.toEmbedding) = edgesIn G A := by
  unfold edgesIn
  rw [← Finset.card_map e.toEquiv.toEmbedding.sym2Map]
  congr 1
  ext z
  induction z using Sym2.ind with
  | h x y =>
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [Finset.mem_map]
    constructor
    · intro hz
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mk_mem_sym2_iff] at hz
      refine ⟨s(x', y'), ?_, rfl⟩
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mk_mem_sym2_iff]
      exact ⟨e.map_adj_iff.mp hz.1, (Finset.mem_map' e.toEquiv.toEmbedding).1 hz.2.1,
        (Finset.mem_map' e.toEquiv.toEmbedding).1 hz.2.2⟩
    · rintro ⟨w, hw, hwz⟩
      induction w using Sym2.ind with
      | h p q =>
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff] at hw
        have hwz' : s(e p, e q) = s(e x', e y') := hwz
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff]
        rcases Sym2.eq_iff.mp hwz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]
          exact ⟨e.map_adj_iff.mpr hw.1, (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.1,
            (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.2⟩
        · rw [← h1, ← h2]
          exact ⟨(e.map_adj_iff.mpr hw.1).symm, (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.2,
            (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.1⟩

/-- `#{A : e_G(A) ≤ t}` is invariant under graph isomorphism. -/
theorem iCount_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (t : ℕ) : iCount G t = iCount H t := by
  unfold iCount
  apply Finset.card_bij (fun A _ => A.map e.toEquiv.toEmbedding)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    rw [edgesIn_map_iso]
    exact hA
  · intro A _ B _ h
    exact Finset.map_injective _ h
  · intro B hB
    refine ⟨B.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      rw [edgesIn_map_iso e.symm]
      exact hB
    · rw [Finset.map_map]
      conv_rhs => rw [← Finset.map_refl (s := B)]
      congr 1
      ext x
      exact e.apply_symm_apply x

/-- `i_γ` is invariant under graph isomorphism. -/
theorem iGamma_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    iGamma G d γ = iGamma H d γ := by
  rw [iGamma_eq_iCount_floor G d hγ, iGamma_eq_iCount_floor H d hγ,
    Fintype.card_congr e.toEquiv]
  exact iCount_iso e _

end General

/-- Adjacency of the switched `K_{d,d}` on `Fin d ⊕ Fin d`. -/
def swAdj {d : ℕ} : Fin d ⊕ Fin d → Fin d ⊕ Fin d → Prop
  | .inl a, .inl b => (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  | .inr a, .inr b => (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  | .inl a, .inr b => ¬ (a.val = b.val ∧ a.val ≤ 1)
  | .inr a, .inl b => ¬ (a.val = b.val ∧ a.val ≤ 1)

/-- The switched `K_{d,d}`: `K_{d,d} - {x₀y₀, x₁y₁} + {x₀x₁, y₀y₁}`. -/
def switchedKdd (d : ℕ) : SimpleGraph (Fin d ⊕ Fin d) where
  Adj := swAdj
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp only [swAdj] at h ⊢ <;> omega⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp only [swAdj] at h <;> omega⟩

instance (d : ℕ) : DecidableRel (switchedKdd d).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)))
  | .inr a, .inr b => inferInstanceAs (Decidable ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)))
  | .inl a, .inr b => inferInstanceAs (Decidable (¬ (a.val = b.val ∧ a.val ≤ 1)))
  | .inr a, .inl b => inferInstanceAs (Decidable (¬ (a.val = b.val ∧ a.val ≤ 1)))

/-- Sanity check: for `d = 3` the switched graph is the prism (same count 28). -/
example : iCount (switchedKdd 3) 1 = 28 := by decide

theorem card_filter_val_eq {d k : ℕ} (hk : k < d) :
    #((univ : Finset (Fin d)).filter (fun b => b.val = k)) = 1 := by
  rw [Finset.card_eq_one]
  exact ⟨⟨k, hk⟩, by ext b; simp [Fin.ext_iff]⟩

theorem card_filter_val_ne {d k : ℕ} (hk : k < d) :
    #((univ : Finset (Fin d)).filter (fun b => ¬ b.val = k)) = d - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin d)))
    (fun b : Fin d => b.val = k)
  rw [card_filter_val_eq hk, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The degree of `v` in `S_d` splits into its neighbours on the two sides. -/
theorem switchedKdd_degree_split {d : ℕ} (v : Fin d ⊕ Fin d) (p q : Fin d → Prop)
    [DecidablePred p] [DecidablePred q]
    (hp : ∀ b, (switchedKdd d).Adj v (.inl b) ↔ p b)
    (hq : ∀ b, (switchedKdd d).Adj v (.inr b) ↔ q b) :
    (switchedKdd d).degree v = #(univ.filter p) + #(univ.filter q) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_disjSum]
  congr 1
  ext w
  cases w with
  | inl b => simp [SimpleGraph.mem_neighborFinset, hp]
  | inr b => simp [SimpleGraph.mem_neighborFinset, hq]

/-- `S_d` is `d`-regular (for `d ≥ 2`). -/
theorem switchedKdd_regular {d : ℕ} (hd : 2 ≤ d) : (switchedKdd d).IsRegularOfDegree d := by
  intro v
  cases v with
  | inl a =>
    by_cases h0 : a.val = 0
    · rw [switchedKdd_degree_split (.inl a) (fun b => b.val = 1) (fun b => ¬ b.val = 0)
        (fun b => by simp only [switchedKdd, swAdj]; omega)
        (fun b => by simp only [switchedKdd, swAdj]; omega),
        card_filter_val_eq (by omega), card_filter_val_ne (by omega)]
      omega
    · by_cases h1 : a.val = 1
      · rw [switchedKdd_degree_split (.inl a) (fun b => b.val = 0) (fun b => ¬ b.val = 1)
          (fun b => by simp only [switchedKdd, swAdj]; omega)
          (fun b => by simp only [switchedKdd, swAdj]; omega),
          card_filter_val_eq (by omega), card_filter_val_ne (by omega)]
        omega
      · rw [switchedKdd_degree_split (.inl a) (fun _ => False) (fun _ => True)
          (fun b => by simp only [switchedKdd, swAdj, iff_false]; omega)
          (fun b => by simp only [switchedKdd, swAdj, iff_true]; omega)]
        simp
  | inr a =>
    by_cases h0 : a.val = 0
    · rw [switchedKdd_degree_split (.inr a) (fun b => ¬ b.val = 0) (fun b => b.val = 1)
        (fun b => by simp only [switchedKdd, swAdj]; omega)
        (fun b => by simp only [switchedKdd, swAdj]; omega),
        card_filter_val_eq (by omega), card_filter_val_ne (by omega)]
      omega
    · by_cases h1 : a.val = 1
      · rw [switchedKdd_degree_split (.inr a) (fun b => ¬ b.val = 1) (fun b => b.val = 0)
          (fun b => by simp only [switchedKdd, swAdj]; omega)
          (fun b => by simp only [switchedKdd, swAdj]; omega),
          card_filter_val_eq (by omega), card_filter_val_ne (by omega)]
        omega
      · rw [switchedKdd_degree_split (.inr a) (fun _ => True) (fun _ => False)
          (fun b => by simp only [switchedKdd, swAdj, iff_true]; omega)
          (fun b => by simp only [switchedKdd, swAdj, iff_false]; omega)]
        simp

/-- **Key inclusion.** Every vertex set spanning at most one edge of `K_{d,d}` spans at most one
edge of `S_d`. -/
theorem edgesIn_switched_le_one {d : ℕ} (A : Finset (Fin d ⊕ Fin d))
    (h : edgesIn (completeBipartiteGraph (Fin d) (Fin d)) A ≤ 1) :
    edgesIn (switchedKdd d) A ≤ 1 := by
  rw [edgesIn_le_one_iff] at h ⊢
  intro u hu v hv u' hu' v' hv' huv hu'v'
  by_cases hmix : (∃ a, Sum.inl a ∈ A) ∧ (∃ b, Sum.inr b ∈ A)
  · -- `A` meets both sides: then `A ⊆ {inl a, inr b}`.
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hmix
    have hall : ∀ w ∈ A, w = Sum.inl a ∨ w = Sum.inr b := by
      intro w hw
      rcases w with c | c
      · left
        have hc := h (Sum.inl a) ha (Sum.inr b) hb (Sum.inl c) hw (Sum.inr b) hb
          (by simp) (by simp)
        rcases Sym2.eq_iff.mp hc with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1.symm
        · exact absurd h1 (by simp)
      · right
        have hc := h (Sum.inl a) ha (Sum.inr b) hb (Sum.inl a) ha (Sum.inr c) hw
          (by simp) (by simp)
        rcases Sym2.eq_iff.mp hc with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2.symm
        · exact absurd h1 (by simp)
    have hne : u ≠ v := (switchedKdd d).ne_of_adj huv
    have hne' : u' ≠ v' := (switchedKdd d).ne_of_adj hu'v'
    rcases hall u hu with rfl | rfl <;> rcases hall v hv with rfl | rfl <;>
      rcases hall u' hu' with rfl | rfl <;> rcases hall v' hv' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact absurd rfl hne'
        | rfl
        | exact Sym2.eq_swap
  · -- `A` is contained in one side: the only possible edges are `x₀x₁` and `y₀y₁`.
    rcases u with a | a <;> rcases v with b | b <;> rcases u' with a' | a' <;>
      rcases v' with b' | b' <;>
      first
        | exact absurd ⟨⟨_, ‹Sum.inl _ ∈ A›⟩, ⟨_, ‹Sum.inr _ ∈ A›⟩⟩ hmix
        | (simp only [switchedKdd, swAdj] at huv hu'v'
           rw [Sym2.eq_iff]
           simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]
           omega)

/-- **Strictness.** `{x₀, y₀, y₂}` spans two edges of `K_{d,d}` but one edge of `S_d`. -/
theorem switched_extra_set {d : ℕ} (hd : 3 ≤ d) :
    ¬ edgesIn (completeBipartiteGraph (Fin d) (Fin d))
        {Sum.inl ⟨0, by omega⟩, Sum.inr ⟨0, by omega⟩, Sum.inr ⟨2, by omega⟩} ≤ 1 ∧
      edgesIn (switchedKdd d)
        {Sum.inl ⟨0, by omega⟩, Sum.inr ⟨0, by omega⟩, Sum.inr ⟨2, by omega⟩} ≤ 1 := by
  constructor
  · rw [edgesIn_le_one_iff]
    intro hK
    have := hK (Sum.inl ⟨0, by omega⟩) (by simp) (Sum.inr ⟨0, by omega⟩) (by simp)
      (Sum.inl ⟨0, by omega⟩) (by simp) (Sum.inr ⟨2, by omega⟩) (by simp) (by simp) (by simp)
    rw [Sym2.eq_iff] at this
    simp at this
  · rw [edgesIn_le_one_iff]
    intro u hu v hv u' hu' v' hv' huv hu'v'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hu' hv'
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
      simp_all [switchedKdd, swAdj, Sym2.eq_swap]

/-- `i_1(K_{d,d}) < i_1(S_d)` for every `d ≥ 3`. -/
theorem iCount_one_lt {d : ℕ} (hd : 3 ≤ d) :
    iCount (completeBipartiteGraph (Fin d) (Fin d)) 1 < iCount (switchedKdd d) 1 := by
  unfold iCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨{Sum.inl ⟨0, by omega⟩, Sum.inr ⟨0, by omega⟩, Sum.inr ⟨2, by omega⟩}, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (switched_extra_set hd).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (switched_extra_set hd).1
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact edgesIn_switched_le_one A hA

/-- One copy of `K_{d,d}` in the `KddUnion` model is Mathlib's `completeBipartiteGraph`. -/
def kddUnionOneIso (d : ℕ) : KddUnion 1 d ≃g completeBipartiteGraph (Fin d) (Fin d) where
  toEquiv := Equiv.uniqueProd (Fin d ⊕ Fin d) (Fin 1)
  map_rel_iff' := by
    intro x y
    show (completeBipartiteGraph (Fin d) (Fin d)).Adj x.2 y.2 ↔ (KddUnion 1 d).Adj x y
    exact ⟨fun h => ⟨Subsingleton.elim _ _, h⟩, fun h => h.2⟩

/-- **Theorem B (qualitative, formal).** For every `d ≥ 3`, Carenini's Question 1.3 fails at
`n = 2d`, `γ = 1/(2d²)` (i.e. `γ d n = 1`): the switched `K_{d,d}` is `d`-regular on `2d`
vertices and has more vertex sets spanning at most one edge than `K_{d,d}`. -/
theorem not_careniniQuestion_two_d {d : ℕ} (hd : 3 ≤ d) :
    ¬ CareniniQuestion (2 * d) d (1 / (2 * (d : ℝ) ^ 2)) := by
  intro h
  have hcard : Fintype.card (Fin d ⊕ Fin d) = 2 * d := by simp; ring
  have h1 := h (Fin d ⊕ Fin d) (switchedKdd d) hcard (switchedKdd_regular (by omega))
  have hdiv : 2 * d / (2 * d) = 1 := Nat.div_self (by omega)
  have hγ : (0 : ℝ) ≤ 1 / (2 * (d : ℝ) ^ 2) := by positivity
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact this.ne'
  have hthr : (1 / (2 * (d : ℝ) ^ 2)) * (d : ℝ) * (Fintype.card (Fin d ⊕ Fin d) : ℝ)
      = ((1 : ℕ) : ℝ) := by
    rw [hcard]; push_cast; field_simp
  have hS : iGamma (switchedKdd d) d (1 / (2 * (d : ℝ) ^ 2)) = iCount (switchedKdd d) 1 :=
    iGamma_eq_iCount _ _ _ hthr
  have hK : iGamma (KddUnion (2 * d / (2 * d)) d) d (1 / (2 * (d : ℝ) ^ 2)) =
      iCount (completeBipartiteGraph (Fin d) (Fin d)) 1 := by
    rw [hdiv, iGamma_iso (kddUnionOneIso d) d hγ]
    exact iGamma_eq_iCount _ _ _ hthr
  rw [hS, hK] at h1
  exact absurd h1 (not_le.mpr (iCount_one_lt hd))

/-! ## Further kernel-checked instances (several copies, bipartite competitors, `d = 2`) -/

/-- The 8-cycle `C_8` on `Fin 8` (bipartite, 2-regular). -/
def C8 : SimpleGraph (Fin 8) where
  Adj i j := (i.val + 1) % 8 = j.val ∨ (j.val + 1) % 8 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel C8.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 8 = j.val ∨ (j.val + 1) % 8 = i.val))

theorem C8_regular : C8.IsRegularOfDegree 2 := by
  intro v; revert v; decide

set_option maxRecDepth 200000 in
theorem iCount_C8_one : iCount C8 1 = 111 := by decide +kernel

set_option maxRecDepth 200000 in
theorem iCount_2C4_one : iCount (KddUnion 2 2) 1 = 105 := by decide +kernel

/-- `d = 2`, `n = 8`, `γ = 1/16` (`γ d n = 1`): `C_8` beats `2 C_4 = 2 K_{2,2}`. -/
theorem not_careniniQuestion_eight_two : ¬ CareniniQuestion 8 2 (1 / 16) := by
  intro h
  have h1 := h (Fin 8) C8 (by simp) C8_regular
  have e1 : iGamma C8 2 (1 / 16) = 111 := by
    rw [iGamma_eq_iCount C8 2 1 (by simp; norm_num)]; exact iCount_C8_one
  have e2 : iGamma (KddUnion (8 / (2 * 2)) 2) 2 (1 / 16) = 105 := by
    show iGamma (KddUnion 2 2) 2 (1 / 16) = 105
    rw [iGamma_eq_iCount (KddUnion 2 2) 2 1 (by simp; norm_num)]; exact iCount_2C4_one
  rw [e1, e2] at h1
  omega

/-- Adjacency of `H_3`: two copies of `K_{3,3}` (sides `{0,1,2} | {3,4,5}` and
`{6,7,8} | {9,10,11}`) with the edges `0–3`, `6–9` removed and `0–9`, `6–3` added. -/
def h3Adj (i j : Fin 12) : Bool :=
  let a := i.val
  let b := j.val
  let cross := (a % 6 < 3) != (b % 6 < 3)
  let same := a / 6 == b / 6
  let removed := (a == 0 && b == 3) || (a == 3 && b == 0) || (a == 6 && b == 9) ||
    (a == 9 && b == 6)
  let added := (a == 0 && b == 9) || (a == 9 && b == 0) || (a == 6 && b == 3) ||
    (a == 3 && b == 6)
  (cross && same && !removed) || added

/-- `H_3`: a connected bipartite cubic graph on 12 vertices. -/
def H3 : SimpleGraph (Fin 12) where
  Adj i j := h3Adj i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel H3.Adj := fun i j => inferInstanceAs (Decidable (h3Adj i j = true))

theorem H3_regular : H3.IsRegularOfDegree 3 := by
  intro v; revert v; decide

/-- `H_3` is bipartite: every edge joins `{i : i % 6 < 3}` to its complement. -/
theorem H3_bipartite : ∀ i j : Fin 12, H3.Adj i j → (i.val % 6 < 3 ↔ ¬ j.val % 6 < 3) := by
  decide

/-- `H_3` is connected: `0–9` joins the two blocks (every vertex is within distance 4 of 0). -/
theorem H3_connected : H3.Connected := by
  have hreach : ∀ v : Fin 12, H3.Reachable 0 v := by
    have a : ∀ i j : Fin 12, H3.Adj i j → (H3.Reachable 0 i → H3.Reachable 0 j) :=
      fun i j hij h0 => h0.trans (SimpleGraph.Adj.reachable hij)
    intro v
    have r0 : H3.Reachable 0 0 := SimpleGraph.Reachable.refl 0
    have r4 := a 0 4 (by decide) r0
    have r5 := a 0 5 (by decide) r0
    have r9 := a 0 9 (by decide) r0
    have r1 := a 4 1 (by decide) r4
    have r2 := a 4 2 (by decide) r4
    have r3 := a 1 3 (by decide) r1
    have r6 := a 3 6 (by decide) r3
    have r10 := a 6 10 (by decide) r6
    have r11 := a 6 11 (by decide) r6
    have r7 := a 9 7 (by decide) r9
    have r8 := a 9 8 (by decide) r9
    fin_cases v <;> assumption
  exact ⟨fun u v => (hreach u).symm.trans (hreach v)⟩

set_option maxRecDepth 200000 in
theorem iCount_H3_one : iCount H3 1 = 527 := by decide +kernel

set_option maxRecDepth 200000 in
theorem iCount_2K33_one : iCount (KddUnion 2 3) 1 = 495 := by decide +kernel

/-- Bipartite, two copies: `n = 12`, `d = 3`, `γ = 1/36` (`γ d n = 1`):
the connected bipartite cubic graph `H_3` beats `2 K_{3,3}`, `527 > 495`. -/
theorem not_careniniQuestion_twelve_bip : ¬ CareniniQuestion 12 3 (1 / 36) := by
  intro h
  have h1 := h (Fin 12) H3 (by simp) H3_regular
  have e1 : iGamma H3 3 (1 / 36) = 527 := by
    rw [iGamma_eq_iCount H3 3 1 (by simp; norm_num)]; exact iCount_H3_one
  have e2 : iGamma (KddUnion (12 / (2 * 3)) 3) 3 (1 / 36) = 495 := by
    show iGamma (KddUnion 2 3) 3 (1 / 36) = 495
    rw [iGamma_eq_iCount (KddUnion 2 3) 3 1 (by simp; norm_num)]; exact iCount_2K33_one
  rw [e1, e2] at h1
  omega

/-- `3 K_4` on `Fin 12`. -/
def threeK4 : SimpleGraph (Fin 12) where
  Adj i j := i ≠ j ∧ i.val / 4 = j.val / 4
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel threeK4.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ i.val / 4 = j.val / 4))

theorem threeK4_regular : threeK4.IsRegularOfDegree 3 := by
  intro v; revert v; decide

set_option maxRecDepth 200000 in
theorem iCount_threeK4_ten : iCount threeK4 10 = 4002 := by decide +kernel

set_option maxRecDepth 200000 in
theorem iCount_2K33_ten : iCount (KddUnion 2 3) 10 = 3981 := by decide +kernel

/-- Theorem A instance with two copies: `n = 12`, `d = 3`, `t* = dn/2 - 3d + 1 = 10`,
`γ = 10/36 = 5/18`: `3 K_4` beats `2 K_{3,3}`, `4002 > 3981`. -/
theorem not_careniniQuestion_twelve_top : ¬ CareniniQuestion 12 3 (5 / 18) := by
  intro h
  have h1 := h (Fin 12) threeK4 (by simp) threeK4_regular
  have e1 : iGamma threeK4 3 (5 / 18) = 4002 := by
    rw [iGamma_eq_iCount threeK4 3 10 (by simp; norm_num)]; exact iCount_threeK4_ten
  have e2 : iGamma (KddUnion (12 / (2 * 3)) 3) 3 (5 / 18) = 3981 := by
    show iGamma (KddUnion 2 3) 3 (5 / 18) = 3981
    rw [iGamma_eq_iCount (KddUnion 2 3) 3 10 (by simp; norm_num)]; exact iCount_2K33_ten
  rw [e1, e2] at h1
  omega

/-- The reference graph `2 K_{3,3}` is indeed 3-regular. -/
theorem KddUnion_two_three_regular : (KddUnion 2 3).IsRegularOfDegree 3 := by
  intro v; revert v; decide

end Carenini

#print axioms Carenini.not_careniniQuestion_six
#print axioms Carenini.prism_beats_K33
#print axioms Carenini.K33Iso
#print axioms Carenini.prismIso
#print axioms Carenini.K33IsoKddUnion
#print axioms Carenini.not_careniniQuestion_two_d
#print axioms Carenini.iCount_one_lt
#print axioms Carenini.switchedKdd_regular
#print axioms Carenini.not_careniniQuestion_eight_two
#print axioms Carenini.not_careniniQuestion_twelve_bip
#print axioms Carenini.not_careniniQuestion_twelve_top
#print axioms Carenini.H3_bipartite
#print axioms Carenini.H3_connected
#print axioms Carenini.KddUnion_two_three_regular
