import Research.Backfill.Paper3.Proof.Poly

/-!
# 2-switches: edge counts and degrees

`H = twoSwitch G u₁ w₁ u₂ w₂` for a valid 2-switch (`G.Adj u₁ w₁`, `G.Adj u₂ w₂`,
`¬ G.Adj u₁ w₂`, `¬ G.Adj u₂ w₁`, `u₁ ≠ w₂`, `u₂ ≠ w₁`). From the pointwise identity of edge
indicators `[e ∈ H] + [e = u₁w₁] + [e = u₂w₂] = [e ∈ G] + [e = u₁w₂] + [e = u₂w₁]` we get
`e_H(A) + [u₁, w₁ ∈ A] + [u₂, w₂ ∈ A] = e_G(A) + [u₁, w₂ ∈ A] + [u₂, w₁ ∈ A]` (summing over the
pairs inside `A`) and `deg_H = deg_G` (summing over the pairs at a vertex).
-/

set_option autoImplicit false

namespace P3L67

open Finset SimpleGraph BackfillPaper3.Challenge

variable {V : Type*}

/-- The side conditions of a 2-switch (those of `TwoSwitchStep`). -/
def ValidSwitch (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) : Prop :=
  G.Adj u₁ w₁ ∧ G.Adj u₂ w₂ ∧ ¬ G.Adj u₁ w₂ ∧ ¬ G.Adj u₂ w₁ ∧ u₁ ≠ w₂ ∧ u₂ ≠ w₁

/-- The edges of a 2-switch. -/
theorem mem_edgeSet_twoSwitch (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) (e : Sym2 V) :
    e ∈ (twoSwitch G u₁ w₁ u₂ w₂).edgeSet ↔
      (e ∈ G.edgeSet ∧ ¬ (e = s(u₁, w₁) ∨ e = s(u₂, w₂))) ∨
        ((e = s(u₁, w₂) ∨ e = s(u₂, w₁)) ∧ ¬ e.IsDiag) := by
  simp only [twoSwitch, edgeSet_sup, edgeSet_deleteEdges, edgeSet_fromEdgeSet, Set.mem_union,
    Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_diagSet]

/-- `e_G(A)` as a sum of edge indicators over the pairs inside `A`. -/
theorem edgesIn_eq_sum [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : edgesIn G A = ∑ e ∈ A.sym2, if e ∈ G.edgeFinset then 1 else 0 := by
  rw [edgesIn, ← Finset.card_filter]
  congr 1
  ext e
  simp only [mem_filter]
  tauto

section Indicator

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u₁ w₁ u₂ w₂ : V}
  {H : SimpleGraph V} [DecidableRel H.Adj]

/-- The pointwise identity of edge indicators for a valid 2-switch `H`. -/
theorem switch_indicator (hH : H = twoSwitch G u₁ w₁ u₂ w₂) (hv : ValidSwitch G u₁ w₁ u₂ w₂)
    (e : Sym2 V) :
    ((if e ∈ H.edgeFinset then 1 else 0) +
        (if e = s(u₁, w₁) then 1 else 0) + (if e = s(u₂, w₂) then 1 else 0) : ℕ) =
      (if e ∈ G.edgeFinset then 1 else 0) + (if e = s(u₁, w₂) then 1 else 0) +
        (if e = s(u₂, w₁) then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  have he1 : s(u₁, w₁) ∈ G.edgeFinset := by rw [mem_edgeFinset]; exact h1
  have he2 : s(u₂, w₂) ∈ G.edgeFinset := by rw [mem_edgeFinset]; exact h2
  have hf1 : s(u₁, w₂) ∉ G.edgeFinset := by rw [mem_edgeFinset]; exact h3
  have hf2 : s(u₂, w₁) ∉ G.edgeFinset := by rw [mem_edgeFinset]; exact h4
  have n12 : s(u₁, w₁) ≠ s(u₂, w₂) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h3 h1
    · exact h5 rfl
  have m12 : s(u₁, w₂) ≠ s(u₂, w₁) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h4 h1
    · exact h1.ne rfl
  have hmem : ∀ f : Sym2 V, f ∈ H.edgeFinset ↔
      (f ∈ G.edgeFinset ∧ f ≠ s(u₁, w₁) ∧ f ≠ s(u₂, w₂)) ∨ f = s(u₁, w₂) ∨ f = s(u₂, w₁) := by
    intro f
    rw [mem_edgeFinset, mem_edgeFinset, hH, mem_edgeSet_twoSwitch]
    constructor
    · rintro (⟨hG, hn⟩ | ⟨hf, -⟩)
      · exact Or.inl ⟨hG, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
      · exact Or.inr hf
    · rintro (⟨hG, n1, n2⟩ | rfl | rfl)
      · exact Or.inl ⟨hG, fun h => h.elim n1 n2⟩
      · exact Or.inr ⟨Or.inl rfl, by simpa using h5⟩
      · exact Or.inr ⟨Or.inr rfl, by simpa using h6⟩
  by_cases a1 : e = s(u₁, w₁)
  · subst a1
    have x1 : s(u₁, w₁) ≠ s(u₁, w₂) := fun h => hf1 (h ▸ he1)
    have x2 : s(u₁, w₁) ≠ s(u₂, w₁) := fun h => hf2 (h ▸ he1)
    have hn : s(u₁, w₁) ∉ H.edgeFinset := by
      rw [hmem]
      rintro (⟨-, h, -⟩ | h | h)
      · exact h rfl
      · exact x1 h
      · exact x2 h
    simp only [hn, he1, n12, x1, x2, ite_true, ite_false, add_zero, zero_add]
  by_cases a2 : e = s(u₂, w₂)
  · subst a2
    have y1 : s(u₂, w₂) ≠ s(u₁, w₂) := fun h => hf1 (h ▸ he2)
    have y2 : s(u₂, w₂) ≠ s(u₂, w₁) := fun h => hf2 (h ▸ he2)
    have hn : s(u₂, w₂) ∉ H.edgeFinset := by
      rw [hmem]
      rintro (⟨-, -, h⟩ | h | h)
      · exact h rfl
      · exact y1 h
      · exact y2 h
    simp only [hn, he2, a1, y1, y2, ite_true, ite_false, add_zero, zero_add]
  by_cases a3 : e = s(u₁, w₂)
  · subst a3
    have hp : s(u₁, w₂) ∈ H.edgeFinset := (hmem _).2 (Or.inr (Or.inl rfl))
    simp only [hp, hf1, a1, a2, m12, ite_true, ite_false, add_zero, zero_add]
  by_cases a4 : e = s(u₂, w₁)
  · subst a4
    have hp : s(u₂, w₁) ∈ H.edgeFinset := (hmem _).2 (Or.inr (Or.inr rfl))
    simp only [hp, hf2, a1, a2, a3, ite_true, ite_false, add_zero, zero_add]
  have hiff : e ∈ H.edgeFinset ↔ e ∈ G.edgeFinset := by
    rw [hmem]
    constructor
    · rintro (⟨h, -, -⟩ | h | h)
      · exact h
      · exact absurd h a3
      · exact absurd h a4
    · intro h
      exact Or.inl ⟨h, a1, a2⟩
  simp only [hiff, a1, a2, a3, a4, ite_false, add_zero]

end Indicator

/-- `Σ_x [s(v, x) = s(p, q)] = [v = p] + [v = q]` for `p ≠ q`. -/
theorem sum_ite_mk_eq [Fintype V] [DecidableEq V] (v p q : V) (hpq : p ≠ q) :
    (∑ x, if s(v, x) = s(p, q) then 1 else 0 : ℕ) =
      (if v = p then 1 else 0) + (if v = q then 1 else 0) := by
  have e : ∀ x, s(v, x) = s(p, q) ↔ (v = p ∧ x = q) ∨ (v = q ∧ x = p) := fun x => Sym2.eq_iff
  by_cases hp : v = p
  · have hq : ¬ v = q := fun h => hpq (hp.symm.trans h)
    have e' : ∀ x, s(v, x) = s(p, q) ↔ x = q := fun x => by rw [e x]; tauto
    simp only [e', Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_eq_left hp, ite_eq_right hq,
      add_zero]
  · by_cases hq : v = q
    · have e' : ∀ x, s(v, x) = s(p, q) ↔ x = p := fun x => by rw [e x]; tauto
      simp only [e', Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_eq_right hp, ite_eq_left hq,
        zero_add]
    · have e' : ∀ x, ¬ s(v, x) = s(p, q) := fun x => by rw [e x]; tauto
      simp only [e', ite_false, Finset.sum_const_zero, ite_eq_right hp, ite_eq_right hq, add_zero]

section Counts

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u₁ w₁ u₂ w₂ : V}
  {H : SimpleGraph V} [DecidableRel H.Adj]

/-- The edge-count identity of a valid 2-switch `H`. -/
theorem edgesIn_twoSwitch (hH : H = twoSwitch G u₁ w₁ u₂ w₂) (hv : ValidSwitch G u₁ w₁ u₂ w₂)
    (A : Finset V) :
    edgesIn H A + (if u₁ ∈ A ∧ w₁ ∈ A then 1 else 0) +
        (if u₂ ∈ A ∧ w₂ ∈ A then 1 else 0) =
      edgesIn G A + (if u₁ ∈ A ∧ w₂ ∈ A then 1 else 0) + (if u₂ ∈ A ∧ w₁ ∈ A then 1 else 0) := by
  have hs : ∀ p q : V, (∑ e ∈ A.sym2, if e = s(p, q) then 1 else 0 : ℕ) =
      if p ∈ A ∧ q ∈ A then 1 else 0 := by
    intro p q
    rw [Finset.sum_ite_eq']
    by_cases h : p ∈ A ∧ q ∈ A
    · rw [ite_eq_left (Finset.mk_mem_sym2_iff.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (Finset.mk_mem_sym2_iff.1 h')), ite_eq_right h]
  rw [edgesIn_eq_sum, edgesIn_eq_sum, ← hs, ← hs, ← hs, ← hs, ← sum_add_distrib,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => switch_indicator hH hv e

/-- A valid 2-switch `H` of `G` has the same degrees as `G`. -/
theorem degree_twoSwitch (hH : H = twoSwitch G u₁ w₁ u₂ w₂) (hv : ValidSwitch G u₁ w₁ u₂ w₂)
    (v : V) : H.degree v = G.degree v := by
  have hdeg : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      K.degree v = ∑ x, if s(v, x) ∈ K.edgeFinset then 1 else 0 := by
    intro K _
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : K.Adj v x
    · rw [ite_eq_left h, ite_eq_left (by rw [mem_edgeFinset]; exact h)]
    · rw [ite_eq_right h, ite_eq_right (by rw [mem_edgeFinset]; exact h)]
  have key := Finset.sum_congr (s₁ := (univ : Finset V)) rfl
    fun x _ => switch_indicator hH hv (s(v, x))
  simp only [Finset.sum_add_distrib] at key
  rw [sum_ite_mk_eq v u₁ w₁ hv.1.ne, sum_ite_mk_eq v u₂ w₂ hv.2.1.ne,
    sum_ite_mk_eq v u₁ w₂ hv.2.2.2.2.1, sum_ite_mk_eq v u₂ w₁ hv.2.2.2.2.2] at key
  rw [hdeg, hdeg]
  omega

end Counts

end P3L67
