import Mathlib
import Research.Backfill.Paper3.Challenge

/-!
# 2-switches: basic facts

For the 2-switch `twoSwitch G u₁ w₁ u₂ w₂` of the challenge file under the side conditions of
`TwoSwitchStep` (collected in `IsSwitch`): the four vertices are distinct; adjacency at `u₁` and
at vertices outside the switch; the inverse switch, so `TwoSwitchStep` is symmetric; and every
vertex keeps its number of neighbours.
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

variable {V : Type*}

/-- The side conditions of a 2-switch, as in `TwoSwitchStep`. -/
structure IsSwitch (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) : Prop where
  adj₁ : G.Adj u₁ w₁
  adj₂ : G.Adj u₂ w₂
  ne₁ : u₁ ≠ w₂
  ne₂ : u₂ ≠ w₁
  nadj₁ : ¬ G.Adj u₁ w₂
  nadj₂ : ¬ G.Adj u₂ w₁

/-- Adjacency in a 2-switch. -/
theorem twoSwitch_adj {G : SimpleGraph V} {u₁ w₁ u₂ w₂ a b : V} :
    (twoSwitch G u₁ w₁ u₂ w₂).Adj a b ↔
      (G.Adj a b ∧ ¬ s(a, b) = s(u₁, w₁) ∧ ¬ s(a, b) = s(u₂, w₂)) ∨
        ((s(a, b) = s(u₁, w₂) ∨ s(a, b) = s(u₂, w₁)) ∧ a ≠ b) := by
  simp only [twoSwitch, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

theorem sym2_ne_of_ne {a b c d : V} (hc : a ≠ c) (hd : a ≠ d) : s(a, b) ≠ s(c, d) := by
  intro h
  have : a ∈ s(c, d) := h ▸ Sym2.mem_mk_left a b
  rcases Sym2.mem_iff.1 this with h' | h'
  · exact hc h'
  · exact hd h'

/-- A vertex outside the switch keeps its neighbours. -/
theorem twoSwitch_adj_of_ne {G : SimpleGraph V} {u₁ w₁ u₂ w₂ a : V}
    (h₁ : a ≠ u₁) (h₂ : a ≠ w₁) (h₃ : a ≠ u₂) (h₄ : a ≠ w₂) (b : V) :
    (twoSwitch G u₁ w₁ u₂ w₂).Adj a b ↔ G.Adj a b := by
  rw [twoSwitch_adj]
  constructor
  · rintro (⟨h, -, -⟩ | ⟨h | h, -⟩)
    · exact h
    · exact absurd h (sym2_ne_of_ne h₁ h₄)
    · exact absurd h (sym2_ne_of_ne h₃ h₂)
  · intro h
    exact Or.inl ⟨h, sym2_ne_of_ne h₁ h₂, sym2_ne_of_ne h₃ h₄⟩

theorem twoSwitch_swap₁ (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) :
    twoSwitch G u₁ w₁ u₂ w₂ = twoSwitch G w₁ u₁ w₂ u₂ := by
  ext a b
  rw [twoSwitch_adj, twoSwitch_adj, Sym2.eq_swap (a := w₁) (b := u₁),
    Sym2.eq_swap (a := w₂) (b := u₂), Sym2.eq_swap (a := w₁) (b := u₂),
    Sym2.eq_swap (a := w₂) (b := u₁)]
  tauto

theorem twoSwitch_swap₂ (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) :
    twoSwitch G u₁ w₁ u₂ w₂ = twoSwitch G u₂ w₂ u₁ w₁ := by
  ext a b
  rw [twoSwitch_adj, twoSwitch_adj]
  tauto

namespace IsSwitch

variable {G : SimpleGraph V} {u₁ w₁ u₂ w₂ : V}

theorem u₁_ne_w₁ (h : IsSwitch G u₁ w₁ u₂ w₂) : u₁ ≠ w₁ := h.adj₁.ne

theorem u₂_ne_w₂ (h : IsSwitch G u₁ w₁ u₂ w₂) : u₂ ≠ w₂ := h.adj₂.ne

theorem u₁_ne_u₂ (h : IsSwitch G u₁ w₁ u₂ w₂) : u₁ ≠ u₂ := by
  rintro rfl
  exact h.nadj₁ h.adj₂

theorem w₁_ne_w₂ (h : IsSwitch G u₁ w₁ u₂ w₂) : w₁ ≠ w₂ := by
  rintro rfl
  exact h.nadj₂ h.adj₂

theorem swap₁ (h : IsSwitch G u₁ w₁ u₂ w₂) : IsSwitch G w₁ u₁ w₂ u₂ where
  adj₁ := h.adj₁.symm
  adj₂ := h.adj₂.symm
  ne₁ := h.ne₂.symm
  ne₂ := h.ne₁.symm
  nadj₁ := fun h' => h.nadj₂ h'.symm
  nadj₂ := fun h' => h.nadj₁ h'.symm

theorem swap₂ (h : IsSwitch G u₁ w₁ u₂ w₂) : IsSwitch G u₂ w₂ u₁ w₁ where
  adj₁ := h.adj₂
  adj₂ := h.adj₁
  ne₁ := h.ne₂
  ne₂ := h.ne₁
  nadj₁ := h.nadj₂
  nadj₂ := h.nadj₁

/-- Adjacency at `u₁` after the switch: `w₁` is replaced by `w₂`. -/
theorem adj_u₁ (hs : IsSwitch G u₁ w₁ u₂ w₂) (b : V) :
    (twoSwitch G u₁ w₁ u₂ w₂).Adj u₁ b ↔ (G.Adj u₁ b ∧ b ≠ w₁) ∨ b = w₂ := by
  rw [twoSwitch_adj]
  simp only [Sym2.congr_right]
  have k₂ : s(u₁, b) ≠ s(u₂, w₂) := sym2_ne_of_ne hs.u₁_ne_u₂ hs.ne₁
  have k₄ : s(u₁, b) ≠ s(u₂, w₁) := sym2_ne_of_ne hs.u₁_ne_u₂ hs.u₁_ne_w₁
  constructor
  · rintro (⟨h, h1, -⟩ | ⟨h | h, -⟩)
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr h
    · exact absurd h k₄
  · rintro (⟨h, h1⟩ | rfl)
    · exact Or.inl ⟨h, h1, k₂⟩
    · exact Or.inr ⟨Or.inl rfl, hs.ne₁⟩

/-- The switch is a `TwoSwitchStep`. -/
theorem step (hs : IsSwitch G u₁ w₁ u₂ w₂) : TwoSwitchStep G (twoSwitch G u₁ w₁ u₂ w₂) :=
  ⟨u₁, w₁, u₂, w₂, hs.adj₁, hs.adj₂, hs.ne₁, hs.ne₂, hs.nadj₁, hs.nadj₂, rfl⟩

/-- The inverse switch is a switch of the switched graph. -/
theorem inv (hs : IsSwitch G u₁ w₁ u₂ w₂) :
    IsSwitch (twoSwitch G u₁ w₁ u₂ w₂) u₁ w₂ u₂ w₁ where
  adj₁ := (hs.adj_u₁ w₂).2 (Or.inr rfl)
  adj₂ := by
    rw [twoSwitch_swap₂ G u₁ w₁ u₂ w₂]
    exact (hs.swap₂.adj_u₁ w₁).2 (Or.inr rfl)
  ne₁ := hs.u₁_ne_w₁
  ne₂ := hs.u₂_ne_w₂
  nadj₁ := by
    rw [hs.adj_u₁]
    rintro (⟨-, h⟩ | h)
    exacts [h rfl, hs.w₁_ne_w₂ h]
  nadj₂ := by
    rw [twoSwitch_swap₂ G u₁ w₁ u₂ w₂, hs.swap₂.adj_u₁]
    rintro (⟨-, h⟩ | h)
    exacts [h rfl, hs.w₁_ne_w₂ h.symm]

/-- Switching back gives the original graph. -/
theorem twoSwitch_twoSwitch (hs : IsSwitch G u₁ w₁ u₂ w₂) :
    twoSwitch (twoSwitch G u₁ w₁ u₂ w₂) u₁ w₂ u₂ w₁ = G := by
  ext a b
  rw [twoSwitch_adj, twoSwitch_adj]
  have hE : ∀ {c d : V}, s(a, b) = s(c, d) → (G.Adj a b ↔ G.Adj c d) := fun h => by
    rw [← SimpleGraph.mem_edgeSet, h, SimpleGraph.mem_edgeSet]
  constructor
  · rintro (⟨⟨h, -⟩ | ⟨h | h, -⟩, h1, h2⟩ | ⟨h | h, -⟩)
    · exact h
    · exact absurd h h1
    · exact absurd h h2
    · exact (hE h).2 hs.adj₁
    · exact (hE h).2 hs.adj₂
  · intro h
    by_cases h1 : s(a, b) = s(u₁, w₁)
    · exact Or.inr ⟨Or.inl h1, h.ne⟩
    by_cases h2 : s(a, b) = s(u₂, w₂)
    · exact Or.inr ⟨Or.inr h2, h.ne⟩
    exact Or.inl ⟨Or.inl ⟨h, h1, h2⟩, fun h3 => hs.nadj₁ ((hE h3).1 h),
      fun h4 => hs.nadj₂ ((hE h4).1 h)⟩

end IsSwitch

theorem isSwitch_of_step {G G' : SimpleGraph V} (h : TwoSwitchStep G G') :
    ∃ u₁ w₁ u₂ w₂, IsSwitch G u₁ w₁ u₂ w₂ ∧ G' = twoSwitch G u₁ w₁ u₂ w₂ := by
  obtain ⟨u₁, w₁, u₂, w₂, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  exact ⟨u₁, w₁, u₂, w₂, ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩

/-- `TwoSwitchStep` is symmetric. -/
theorem step_symm {G G' : SimpleGraph V} (h : TwoSwitchStep G G') : TwoSwitchStep G' G := by
  obtain ⟨u₁, w₁, u₂, w₂, hs, rfl⟩ := isSwitch_of_step h
  have := hs.inv.step
  rwa [hs.twoSwitch_twoSwitch] at this

/-- Reachability by 2-switches is symmetric. -/
theorem reach_symm {G H : SimpleGraph V} (h : Relation.ReflTransGen TwoSwitchStep G H) :
    Relation.ReflTransGen TwoSwitchStep H G := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .head (step_symm hst) ih

section Degrees

variable [Fintype V]

open Classical in
/-- The neighbours of `v` (with classical decidability, so that it applies to every graph). -/
noncomputable def nbr (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter (G.Adj v)

theorem mem_nbr {G : SimpleGraph V} {v w : V} : w ∈ nbr G v ↔ G.Adj v w := by
  simp [nbr]

theorem card_nbr_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (nbr G v).card = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext t
  rw [mem_nbr, SimpleGraph.mem_neighborFinset]

variable [DecidableEq V] {G : SimpleGraph V} {u₁ w₁ u₂ w₂ : V}

theorem IsSwitch.nbr_u₁ (hs : IsSwitch G u₁ w₁ u₂ w₂) :
    nbr (twoSwitch G u₁ w₁ u₂ w₂) u₁ = insert w₂ ((nbr G u₁).erase w₁) := by
  ext b
  rw [mem_nbr, hs.adj_u₁, Finset.mem_insert, Finset.mem_erase, mem_nbr]
  tauto

theorem IsSwitch.card_nbr_u₁ (hs : IsSwitch G u₁ w₁ u₂ w₂) :
    (nbr (twoSwitch G u₁ w₁ u₂ w₂) u₁).card = (nbr G u₁).card := by
  have hw₁ : w₁ ∈ nbr G u₁ := mem_nbr.2 hs.adj₁
  rw [hs.nbr_u₁, Finset.card_insert_of_notMem, Finset.card_erase_of_mem hw₁]
  · have : 0 < (nbr G u₁).card := Finset.card_pos.2 ⟨w₁, hw₁⟩
    omega
  · rw [Finset.mem_erase, mem_nbr]
    exact fun h => hs.nadj₁ h.2

/-- A 2-switch keeps the number of neighbours of every vertex. -/
theorem IsSwitch.card_nbr (hs : IsSwitch G u₁ w₁ u₂ w₂) (v : V) :
    (nbr (twoSwitch G u₁ w₁ u₂ w₂) v).card = (nbr G v).card := by
  by_cases h1 : v = u₁
  · subst h1
    exact hs.card_nbr_u₁
  by_cases h2 : v = w₁
  · subst h2
    rw [twoSwitch_swap₁]
    exact hs.swap₁.card_nbr_u₁
  by_cases h3 : v = u₂
  · subst h3
    rw [twoSwitch_swap₂]
    exact hs.swap₂.card_nbr_u₁
  by_cases h4 : v = w₂
  · subst h4
    rw [twoSwitch_swap₁, twoSwitch_swap₂]
    exact hs.swap₁.swap₂.card_nbr_u₁
  congr 1
  ext b
  rw [mem_nbr, mem_nbr, twoSwitch_adj_of_ne h1 h2 h3 h4]

theorem card_nbr_of_step {G G' : SimpleGraph V} (h : TwoSwitchStep G G') (v : V) :
    (nbr G' v).card = (nbr G v).card := by
  obtain ⟨u₁, w₁, u₂, w₂, hs, rfl⟩ := isSwitch_of_step h
  exact hs.card_nbr v

end Degrees

end P3TS
