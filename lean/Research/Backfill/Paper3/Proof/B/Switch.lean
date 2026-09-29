import Research.Backfill.Paper3.Proof.Tier0

/-!
# 2-switches

For a valid 2-switch `H = twoSwitch G u₁ w₁ u₂ w₂` (`G.Adj u₁ w₁`, `G.Adj u₂ w₂`, `¬ G.Adj u₁ w₂`,
`¬ G.Adj u₂ w₁`, `u₁ ≠ w₂`, `u₂ ≠ w₁`): a pointwise identity for edge indicators on `Sym2 V`, the
edge-count identity `e_H(A) + [u₁,w₁ ∈ A] + [u₂,w₂ ∈ A] = e_G(A) + [u₁,w₂ ∈ A] + [u₂,w₁ ∈ A]`,
and preservation of degrees. Also: transport of a 2-switch along an isomorphism, automorphisms
of `K_{d,d}` and of `m` copies of a graph, `KddUnion 1 d ≅ K_{d,d}`, and regularity of `K_{d,d}`.
-/

set_option autoImplicit false

namespace P3B

open Finset SimpleGraph BackfillPaper3.Challenge

variable {V W : Type*}

/-- The side conditions of a 2-switch. -/
structure ValidSwitch (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) : Prop where
  adj₁ : G.Adj u₁ w₁
  adj₂ : G.Adj u₂ w₂
  nadj₁ : ¬ G.Adj u₁ w₂
  nadj₂ : ¬ G.Adj u₂ w₁
  ne₁ : u₁ ≠ w₂
  ne₂ : u₂ ≠ w₁

theorem twoSwitch_adj {G : SimpleGraph V} {u₁ w₁ u₂ w₂ a b : V} :
    (twoSwitch G u₁ w₁ u₂ w₂).Adj a b ↔
      (G.Adj a b ∧ ¬ s(a, b) = s(u₁, w₁) ∧ ¬ s(a, b) = s(u₂, w₂)) ∨
        ((s(a, b) = s(u₁, w₂) ∨ s(a, b) = s(u₂, w₁)) ∧ a ≠ b) := by
  simp only [twoSwitch, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

theorem mem_edgeSet_twoSwitch {G : SimpleGraph V} {u₁ w₁ u₂ w₂ : V} (z : Sym2 V) :
    z ∈ (twoSwitch G u₁ w₁ u₂ w₂).edgeSet ↔
      (z ∈ G.edgeSet ∧ ¬ z = s(u₁, w₁) ∧ ¬ z = s(u₂, w₂)) ∨
        ((z = s(u₁, w₂) ∨ z = s(u₂, w₁)) ∧ ¬ z.IsDiag) := by
  simp only [twoSwitch, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
    SimpleGraph.edgeSet_fromEdgeSet, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sym2.mem_diagSet, not_or]

namespace ValidSwitch

variable {G : SimpleGraph V} {u₁ w₁ u₂ w₂ : V}

theorem e_ne (h : ValidSwitch G u₁ w₁ u₂ w₂) : s(u₁, w₁) ≠ s(u₂, w₂) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact h.nadj₁ (h1 ▸ h2 ▸ h.adj₂)
  · exact h.ne₁ h1

theorem f_ne (h : ValidSwitch G u₁ w₁ u₂ w₂) : s(u₁, w₂) ≠ s(u₂, w₁) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact h.nadj₁ (h2 ▸ h.adj₁)
  · exact h.adj₁.ne h1

/-- Pointwise identity: `[z ∈ E(H)] + [z = u₁w₁] + [z = u₂w₂] = [z ∈ E(G)] + [z = u₁w₂] + [z = u₂w₁]`. -/
theorem ind [DecidableEq V] [DecidableRel G.Adj] (h : ValidSwitch G u₁ w₁ u₂ w₂) (z : Sym2 V) :
    ((if z ∈ (twoSwitch G u₁ w₁ u₂ w₂).edgeSet then 1 else 0) +
        (if z = s(u₁, w₁) then 1 else 0) + (if z = s(u₂, w₂) then 1 else 0) : ℕ) =
      (if z ∈ G.edgeSet then 1 else 0) + (if z = s(u₁, w₂) then 1 else 0) +
        (if z = s(u₂, w₁) then 1 else 0) := by
  have e1 : s(u₁, w₁) ∈ G.edgeSet := h.adj₁
  have e2 : s(u₂, w₂) ∈ G.edgeSet := h.adj₂
  have f1 : s(u₁, w₂) ∉ G.edgeSet := h.nadj₁
  have f2 : s(u₂, w₁) ∉ G.edgeSet := h.nadj₂
  have d1 : ¬ s(u₁, w₂).IsDiag := by rw [Sym2.mk_isDiag_iff]; exact h.ne₁
  have d2 : ¬ s(u₂, w₁).IsDiag := by rw [Sym2.mk_isDiag_iff]; exact h.ne₂
  have e12 := h.e_ne
  have f12 := h.f_ne
  have n11 : s(u₁, w₁) ≠ s(u₁, w₂) := fun he => f1 (he ▸ e1)
  have n12 : s(u₁, w₁) ≠ s(u₂, w₁) := fun he => f2 (he ▸ e1)
  have n21 : s(u₂, w₂) ≠ s(u₁, w₂) := fun he => f1 (he ▸ e2)
  have n22 : s(u₂, w₂) ≠ s(u₂, w₁) := fun he => f2 (he ▸ e2)
  simp only [mem_edgeSet_twoSwitch]
  by_cases h1 : z = s(u₁, w₁)
  · subst h1
    simp only [e1, e12, n11, n12, not_true_eq_false, false_and, and_false, or_self, ite_true,
      ite_false]
  by_cases h2 : z = s(u₂, w₂)
  · subst h2
    simp only [e2, e12.symm, n21, n22, not_true_eq_false, false_and, and_false, or_self,
      ite_true, ite_false]
  by_cases h3 : z = s(u₁, w₂)
  · subst h3
    simp only [f1, d1, f12, n11.symm, n21.symm, not_false_eq_true, and_true, true_or, or_true,
      ite_true, ite_false]
  by_cases h4 : z = s(u₂, w₁)
  · subst h4
    simp only [f2, d2, f12.symm, n12.symm, n22.symm, not_false_eq_true, and_true, or_true,
      ite_true, ite_false]
  simp only [h1, h2, h3, h4, not_false_eq_true, and_true, or_self, false_and, or_false,
    ite_false, add_zero]

end ValidSwitch

section Counting

variable [Fintype V] [DecidableEq V]

/-- `e_G(A) = Σ_{z ∈ A.sym2} [z ∈ E(G)]`. -/
theorem edgesIn_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    edgesIn G A = ∑ z ∈ A.sym2, if z ∈ G.edgeSet then 1 else 0 := by
  rw [edgesIn, ← Finset.card_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  exact and_comm

omit [Fintype V] in
theorem sum_sym2_ite_eq (A : Finset V) (u w : V) :
    (∑ z ∈ A.sym2, if z = s(u, w) then 1 else 0 : ℕ) = if u ∈ A ∧ w ∈ A then 1 else 0 := by
  simp only [Finset.sum_ite_eq', Finset.mk_mem_sym2_iff]

/-- The edge-count identity of a valid 2-switch. -/
theorem ValidSwitch.edgesIn_eq {G : SimpleGraph V} [DecidableRel G.Adj] {u₁ w₁ u₂ w₂ : V}
    (h : ValidSwitch G u₁ w₁ u₂ w₂) (A : Finset V) :
    edgesIn (twoSwitch G u₁ w₁ u₂ w₂) A + (if u₁ ∈ A ∧ w₁ ∈ A then 1 else 0) +
        (if u₂ ∈ A ∧ w₂ ∈ A then 1 else 0) =
      edgesIn G A + (if u₁ ∈ A ∧ w₂ ∈ A then 1 else 0) + (if u₂ ∈ A ∧ w₁ ∈ A then 1 else 0) := by
  rw [edgesIn_eq_sum, edgesIn_eq_sum, ← sum_sym2_ite_eq A u₁ w₁, ← sum_sym2_ite_eq A u₂ w₂,
    ← sum_sym2_ite_eq A u₁ w₂, ← sum_sym2_ite_eq A u₂ w₁, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ => h.ind z

omit [DecidableEq V] in
/-- `deg_G v = Σ_w [vw ∈ E(G)]`. -/
theorem degree_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ w, if s(v, w) ∈ G.edgeSet then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]
  simp only [SimpleGraph.mem_edgeSet]

/-- `Σ_w [s(v, w) = s(a, b)] = [v = a] + [v = b]` for `a ≠ b`. -/
theorem sum_ite_mk_eq (v a b : V) (hab : a ≠ b) :
    (∑ w, if s(v, w) = s(a, b) then 1 else 0 : ℕ) =
      (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  by_cases hva : v = a
  · subst hva
    have hvb : v ≠ b := hab
    have hw : ∀ w, (s(v, w) = s(v, b) ↔ w = b) := fun w => Sym2.congr_right
    simp only [hw, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hvb, ite_false]
  · by_cases hvb : v = b
    · subst hvb
      have hw : ∀ w, (s(v, w) = s(a, v) ↔ w = a) := by
        intro w
        rw [Sym2.eq_iff]
        constructor
        · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact absurd h1 hva
          · exact h2
        · intro hw
          exact Or.inr ⟨rfl, hw⟩
      simp only [hw, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hva, ite_false]
    · have hw : ∀ w, ¬ s(v, w) = s(a, b) := by
        intro w he
        rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hva h1
        · exact hvb h1
      simp only [hw, ite_false, Finset.sum_const_zero, hva, hvb, add_zero]

/-- A valid 2-switch preserves every degree. -/
theorem ValidSwitch.degree_eq {G : SimpleGraph V} [DecidableRel G.Adj] {u₁ w₁ u₂ w₂ : V}
    (h : ValidSwitch G u₁ w₁ u₂ w₂) (v : V) :
    (twoSwitch G u₁ w₁ u₂ w₂).degree v = G.degree v := by
  have key := Finset.sum_congr (rfl : (univ : Finset V) = univ) fun w _ => h.ind s(v, w)
  simp only [Finset.sum_add_distrib] at key
  rw [sum_ite_mk_eq v u₁ w₁ h.adj₁.ne, sum_ite_mk_eq v u₂ w₂ h.adj₂.ne,
    sum_ite_mk_eq v u₁ w₂ h.ne₁, sum_ite_mk_eq v u₂ w₁ h.ne₂, ← degree_eq_sum,
    ← degree_eq_sum] at key
  omega

theorem ValidSwitch.isRegularOfDegree {G : SimpleGraph V} [DecidableRel G.Adj]
    {u₁ w₁ u₂ w₂ : V} (h : ValidSwitch G u₁ w₁ u₂ w₂) {k : ℕ} (hG : G.IsRegularOfDegree k) :
    (twoSwitch G u₁ w₁ u₂ w₂).IsRegularOfDegree k :=
  fun v => (h.degree_eq v).trans (hG v)

end Counting

/-! ## Isomorphisms -/

/-- A 2-switch transported along an isomorphism. -/
def twoSwitchIso {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G') (u₁ w₁ u₂ w₂ : V) :
    twoSwitch G u₁ w₁ u₂ w₂ ≃g twoSwitch G' (φ u₁) (φ w₁) (φ u₂) (φ w₂) where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    have hinj : ∀ x y p q : V, s(φ x, φ y) = s(φ p, φ q) ↔ s(x, y) = s(p, q) := by
      intro x y p q
      simp only [Sym2.eq_iff, φ.injective.eq_iff]
    change (twoSwitch G' _ _ _ _).Adj (φ a) (φ b) ↔ _
    rw [twoSwitch_adj, twoSwitch_adj, hinj, hinj, hinj, hinj, φ.map_adj_iff,
      φ.injective.ne_iff]

theorem nonempty_twoSwitch_iso {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G')
    {u₁ w₁ u₂ w₂ : V} {u₁' w₁' u₂' w₂' : W} (h₁ : φ u₁ = u₁') (h₂ : φ w₁ = w₁')
    (h₃ : φ u₂ = u₂') (h₄ : φ w₂ = w₂') :
    Nonempty (twoSwitch G u₁ w₁ u₂ w₂ ≃g twoSwitch G' u₁' w₁' u₂' w₂') := by
  subst h₁ h₂ h₃ h₄
  exact ⟨twoSwitchIso φ u₁ w₁ u₂ w₂⟩

/-- A permutation sending a given pair of distinct points to another. -/
theorem exists_perm_pair {α : Type*} [DecidableEq α] {a₁ a₂ c₁ c₂ : α} (ha : a₁ ≠ a₂)
    (hc : c₁ ≠ c₂) : ∃ σ : Equiv.Perm α, σ a₁ = c₁ ∧ σ a₂ = c₂ := by
  refine ⟨Equiv.swap (Equiv.swap a₁ c₁ a₂) c₂ * Equiv.swap a₁ c₁, ?_, ?_⟩
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have h' : Equiv.swap a₁ c₁ a₂ = Equiv.swap a₁ c₁ a₁ := by
        rw [Equiv.swap_apply_left]
        exact h.symm
      exact ha ((Equiv.swap a₁ c₁).injective h').symm
    · exact hc
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]

/-- `Sum.map σ τ` is an automorphism of `K_{d,d}`. -/
def kddIso {d : ℕ} (σ τ : Equiv.Perm (Fin d)) : Kdd d ≃g Kdd d where
  toEquiv := Equiv.sumCongr σ τ
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> simp

/-- A family of automorphisms of `G` gives an automorphism of `m G`. -/
def copiesIso {m : ℕ} {G : SimpleGraph W} (ψ : Fin m → (G ≃g G)) : copies m G ≃g copies m G where
  toEquiv := Equiv.prodShear (Equiv.refl _) fun i => (ψ i).toEquiv
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    change (copies m G).Adj (i, ψ i x) (j, ψ j y) ↔ (copies m G).Adj (i, x) (j, y)
    rw [SimpleGraph.boxProd_adj, SimpleGraph.boxProd_adj]
    simp only [SimpleGraph.bot_adj, false_and, false_or]
    constructor
    · rintro ⟨hadj, rfl⟩
      exact ⟨(ψ i).map_adj_iff.mp hadj, rfl⟩
    · rintro ⟨hadj, rfl⟩
      exact ⟨(ψ i).map_adj_iff.mpr hadj, rfl⟩

/-- One copy of `K_{d,d}` is `K_{d,d}`. -/
def kddUnionOneIso (d : ℕ) : KddUnion 1 d ≃g Kdd d where
  toEquiv := Equiv.uniqueProd (Fin d ⊕ Fin d) (Fin 1)
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    change (Kdd d).Adj x y ↔ (KddUnion 1 d).Adj (i, x) (i, y)
    rw [SimpleGraph.boxProd_adj]
    simp only [SimpleGraph.bot_adj, false_and, false_or, and_true]

/-- `K_{d,d}` is `d`-regular. -/
theorem kdd_regular (d : ℕ) : (Kdd d).IsRegularOfDegree d := by
  intro v
  rw [degree_eq_sum, Fintype.sum_sum_type]
  cases v <;> simp

end P3B
