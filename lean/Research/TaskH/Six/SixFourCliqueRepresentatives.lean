import Research.TaskH.Six.SixFourCliquePacking

/-! One actual representative for every nonempty singleton attachment class. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def fourCliqueSingleGroup (G : SimpleGraph V) (q : Fin 4 → V)
    (i : Fin 4) : Finset V :=
  (fourCliqueSet q)ᶜ.filter (fun x => fourCliqueLabels G q x = {i})

noncomputable def fourCliqueActiveLabels (G : SimpleGraph V) (q : Fin 4 → V) :
    Finset (Fin 4) := Finset.univ.filter (fun i => (fourCliqueSingleGroup G q i).Nonempty)

noncomputable def fourCliqueRepresentative (G : SimpleGraph V) (q : Fin 4 → V)
    (i : Fin 4) : V :=
  if h : (fourCliqueSingleGroup G q i).Nonempty then h.choose else q 0

noncomputable def fourCliqueRepresentatives (G : SimpleGraph V) (q : Fin 4 → V) :
    Finset V := (fourCliqueActiveLabels G q).image (fourCliqueRepresentative G q)

theorem fourCliqueRepresentative_mem (q : Fin 4 → V) (i : Fin 4)
    (hi : i ∈ fourCliqueActiveLabels G q) :
    fourCliqueRepresentative G q i ∈ fourCliqueSingleGroup G q i := by
  have hn : (fourCliqueSingleGroup G q i).Nonempty := (Finset.mem_filter.mp hi).2
  unfold fourCliqueRepresentative
  split
  · rename_i h
    exact h.choose_spec
  · rename_i h
    exact False.elim (h hn)

theorem fourCliqueRepresentative_labels (q : Fin 4 → V) (i : Fin 4)
    (hi : i ∈ fourCliqueActiveLabels G q) :
    fourCliqueLabels G q (fourCliqueRepresentative G q i) = {i} := by
  exact (Finset.mem_filter.mp (fourCliqueRepresentative_mem q i hi)).2

theorem fourCliqueRepresentative_outside (q : Fin 4 → V) (i : Fin 4)
    (hi : i ∈ fourCliqueActiveLabels G q) :
    fourCliqueRepresentative G q i ∉ fourCliqueSet q := by
  exact Finset.mem_compl.mp
    (Finset.mem_filter.mp (fourCliqueRepresentative_mem q i hi)).1

theorem fourCliqueRepresentative_injOn (q : Fin 4 → V) :
    Set.InjOn (fourCliqueRepresentative G q) (fourCliqueActiveLabels G q) := by
  intro i hi j hj he
  have h1 := fourCliqueRepresentative_labels q i hi
  have h2 := fourCliqueRepresentative_labels q j hj
  rw [he, h2] at h1
  exact Finset.singleton_inj.mp h1.symm

theorem fourCliqueRepresentatives_card (q : Fin 4 → V) :
    (fourCliqueRepresentatives G q).card = (fourCliqueActiveLabels G q).card := by
  exact Finset.card_image_of_injOn (fourCliqueRepresentative_injOn q)

theorem fourCliqueActiveLabels_card_le_four (q : Fin 4 → V) :
    (fourCliqueActiveLabels G q).card ≤ 4 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem fourCliqueRepresentatives_outside (q : Fin 4 → V) :
    ∀ x ∈ fourCliqueRepresentatives G q, x ∉ fourCliqueSet q := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact fourCliqueRepresentative_outside q i hi

theorem fourCliqueRepresentatives_single (q : Fin 4 → V) :
    ∀ x ∈ fourCliqueRepresentatives G q, (fourCliqueLabels G q x).card = 1 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [fourCliqueRepresentative_labels q i hi]
  simp

theorem fourCliqueRepresentatives_distinct_labels (q : Fin 4 → V) :
    ∀ x ∈ fourCliqueRepresentatives G q, ∀ y ∈ fourCliqueRepresentatives G q, x ≠ y →
      fourCliqueLabels G q x ≠ fourCliqueLabels G q y := by
  intro x hx y hy hxy he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rw [fourCliqueRepresentative_labels q i hi, fourCliqueRepresentative_labels q j hj] at he
  exact hxy (congrArg (fourCliqueRepresentative G q) (Finset.singleton_inj.mp he))

variable [DecidableRel G.Adj]

theorem fourClique_full_open_packing
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x) :
    (δ - 4) * (fourCliqueMulti G q).card +
      (δ - 1) * (fourCliqueActiveLabels G q).card ≤ Fintype.card V - 4 := by
  have hh := fourClique_selected_open_packing hcrit hr hn q hq hclique δ hdegree
    (fourCliqueRepresentatives G q) (fourCliqueRepresentatives_outside q)
    (fourCliqueRepresentatives_single q) (fourCliqueRepresentatives_distinct_labels q)
  rwa [fourCliqueRepresentatives_card q] at hh

omit [Fintype V] in
theorem fourClique_root_internal_neighbors_card (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) (i : Fin 4) :
    (packingNeighborsIn G (fourCliqueSet q) (q i)).card = 3 := by
  rw [fourClique_internal_neighbors_card q hq]
  have he : fourCliqueLabels G q (q i) = (Finset.univ : Finset (Fin 4)).erase i := by
    ext j
    simp only [fourCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hij hji
      subst j
      exact G.loopless.irrefl _ hij
    · intro hji
      exact hclique i j hji.symm
  rw [he, Finset.card_erase_of_mem (Finset.mem_univ i)]
  norm_num

theorem fourClique_missing_singleton_many_multi (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x)
    (hp : (fourCliqueActiveLabels G q).card < 4) :
    δ - 3 ≤ (fourCliqueMulti G q).card := by
  classical
  have hlt : (fourCliqueActiveLabels G q).card <
      (Finset.univ : Finset (Fin 4)).card := by simpa using hp
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hnone : ¬ (fourCliqueSingleGroup G q i).Nonempty := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsub : packingNeighborsIn G (fourCliqueSet q)ᶜ (q i) ⊆ fourCliqueMulti G q := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    have hiL : i ∈ fourCliqueLabels G q x := by
      simpa only [fourCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and]
        using hh.2.symm
    have hl : 2 ≤ (fourCliqueLabels G q x).card := by
      by_contra hsmall
      have hle : (fourCliqueLabels G q x).card ≤ 1 := by omega
      have he : fourCliqueLabels G q x = {i} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hiL, fun j hj => Finset.card_le_one.mp hle j hj i hiL⟩
      apply hnone
      exact ⟨x, Finset.mem_filter.mpr ⟨hh.1, he⟩⟩
    exact Finset.mem_filter.mpr ⟨hh.1, hl⟩
  have hout : δ - 3 ≤ (packingNeighborsIn G (fourCliqueSet q)ᶜ (q i)).card :=
    packingNeighborsIn_compl_lower (fourCliqueSet q) (q i) δ 3 (hdegree _)
      (fourClique_root_internal_neighbors_card q hq hclique i).le
  exact hout.trans (Finset.card_le_card hsub)

end TaskH.Six

#print axioms TaskH.Six.fourCliqueSingleGroup
#print axioms TaskH.Six.fourCliqueActiveLabels
#print axioms TaskH.Six.fourCliqueRepresentative
#print axioms TaskH.Six.fourCliqueRepresentatives
#print axioms TaskH.Six.fourCliqueRepresentative_mem
#print axioms TaskH.Six.fourCliqueRepresentative_labels
#print axioms TaskH.Six.fourCliqueRepresentative_outside
#print axioms TaskH.Six.fourCliqueRepresentative_injOn
#print axioms TaskH.Six.fourCliqueRepresentatives_card
#print axioms TaskH.Six.fourCliqueActiveLabels_card_le_four
#print axioms TaskH.Six.fourCliqueRepresentatives_outside
#print axioms TaskH.Six.fourCliqueRepresentatives_single
#print axioms TaskH.Six.fourCliqueRepresentatives_distinct_labels
#print axioms TaskH.Six.fourClique_full_open_packing
#print axioms TaskH.Six.fourClique_root_internal_neighbors_card
#print axioms TaskH.Six.fourClique_missing_singleton_many_multi
