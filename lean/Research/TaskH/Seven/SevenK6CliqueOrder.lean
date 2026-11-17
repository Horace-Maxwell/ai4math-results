import Research.TaskH.Seven.SevenK6CliqueThreeHooks

/-! A six-clique in the noncomplete original branch forces order at least
fifteen, before any clone/common-neighbor deleted coloring is chosen. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem six_clique_neighbors_card (q : Fin 6 → V) (hq : Function.Injective q) (x : V) :
    (packingNeighborsIn G (sixCliqueSet q) x).card = (sixCliqueHooks G q x).card := by
  classical
  have he : packingNeighborsIn G (sixCliqueSet q) x = (sixCliqueHooks G q x).image q := by
    ext z
    simp only [packingNeighborsIn, sixCliqueSet, sixCliqueHooks, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hxi⟩
      exact ⟨i, hxi, rfl⟩
    · rintro ⟨i, hxi, rfl⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
  rw [he, Finset.card_image_of_injective _ hq]

omit [Fintype V] in
theorem six_clique_root_inside_card_le_five (q : Fin 6 → V)
    (hq : Function.Injective q) (i : Fin 6) :
    (packingNeighborsIn G (sixCliqueSet q) (q i)).card ≤ 5 := by
  classical
  have hmem : q i ∈ sixCliqueSet q := (mem_sixCliqueSet q _).mpr ⟨i, rfl⟩
  have hsub : packingNeighborsIn G (sixCliqueSet q) (q i) ⊆ (sixCliqueSet q).erase (q i) := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
  have hh := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hmem, sixCliqueSet_card q hq] at hh


theorem critical_six_clique_card_ge_fifteen
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hc : modCycleCount 7 G = 2880) (hn : 9 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    15 ≤ Fintype.card V := by
  classical
  let Q := sixCliqueSet q
  have hQ : Q.card = 6 := sixCliqueSet_card q hq
  have hrow : ∀ x ∈ Q, 3 ≤ (packingNeighborsIn G Qᶜ x).card := by
    intro x hx
    obtain ⟨i, rfl⟩ := (mem_sixCliqueSet q x).mp hx
    exact packingNeighborsIn_compl_lower Q (q i) 8 5 (hdegree _)
      (six_clique_root_inside_card_le_five q hq i)
  have hcol : ∀ x ∈ Qᶜ, (packingNeighborsIn G Q x).card ≤ 2 := by
    intro x hx
    rw [six_clique_neighbors_card q hq x]
    apply critical_six_clique_hooks_card_le_two hcrit hs hr hc hn q hq hclique x
    intro i hi
    exact (Finset.mem_compl.mp hx) ((mem_sixCliqueSet q x).mpr ⟨i, hi.symm⟩)
  have hlow : 18 ≤ ∑ x ∈ Q, (packingNeighborsIn G Qᶜ x).card := by
    calc
      18 = ∑ _x ∈ Q, 3 := by simp [hQ]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhigh : (∑ x ∈ Qᶜ, (packingNeighborsIn G Q x).card) ≤ 2 * Qᶜ.card := by
    calc
      _ ≤ ∑ _x ∈ Qᶜ, 2 := Finset.sum_le_sum hcol
      _ = _ := by simp [Nat.mul_comm]
  have hcross := seven_cross_neighbors_double_count (G := G) Q
  have hcard := Finset.card_add_card_compl Q
  rw [hQ] at hcard
  omega

end TaskH.Seven
#print axioms TaskH.Seven.six_clique_neighbors_card
#print axioms TaskH.Seven.six_clique_root_inside_card_le_five
#print axioms TaskH.Seven.critical_six_clique_card_ge_fifteen
