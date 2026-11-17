import Research.TaskH.Seven.SevenK5PackingLabels

/-! One actual representative for every nonempty singleton attachment class. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def fiveCliqueSingleGroup (G : SimpleGraph V) (q : Fin 5 → V)
    (i : Fin 5) : Finset V :=
  (fiveCliqueSet q)ᶜ.filter (fun x => fiveCliqueLabels G q x = {i})

noncomputable def fiveCliqueActiveLabels (G : SimpleGraph V) (q : Fin 5 → V) :
    Finset (Fin 5) := Finset.univ.filter (fun i => (fiveCliqueSingleGroup G q i).Nonempty)

noncomputable def fiveCliqueRepresentative (G : SimpleGraph V) (q : Fin 5 → V)
    (i : Fin 5) : V :=
  if h : (fiveCliqueSingleGroup G q i).Nonempty then h.choose else q 0

noncomputable def fiveCliqueRepresentatives (G : SimpleGraph V) (q : Fin 5 → V) :
    Finset V := (fiveCliqueActiveLabels G q).image (fiveCliqueRepresentative G q)

theorem fiveCliqueRepresentative_mem (q : Fin 5 → V) (i : Fin 5)
    (hi : i ∈ fiveCliqueActiveLabels G q) :
    fiveCliqueRepresentative G q i ∈ fiveCliqueSingleGroup G q i := by
  have hn : (fiveCliqueSingleGroup G q i).Nonempty := (Finset.mem_filter.mp hi).2
  unfold fiveCliqueRepresentative
  split
  · rename_i h
    exact h.choose_spec
  · rename_i h
    exact False.elim (h hn)

theorem fiveCliqueRepresentative_labels (q : Fin 5 → V) (i : Fin 5)
    (hi : i ∈ fiveCliqueActiveLabels G q) :
    fiveCliqueLabels G q (fiveCliqueRepresentative G q i) = {i} := by
  exact (Finset.mem_filter.mp (fiveCliqueRepresentative_mem q i hi)).2

theorem fiveCliqueRepresentative_outside (q : Fin 5 → V) (i : Fin 5)
    (hi : i ∈ fiveCliqueActiveLabels G q) :
    fiveCliqueRepresentative G q i ∉ fiveCliqueSet q := by
  exact Finset.mem_compl.mp
    (Finset.mem_filter.mp (fiveCliqueRepresentative_mem q i hi)).1

theorem fiveCliqueRepresentative_injOn (q : Fin 5 → V) :
    Set.InjOn (fiveCliqueRepresentative G q) (fiveCliqueActiveLabels G q) := by
  intro i hi j hj he
  have h1 := fiveCliqueRepresentative_labels q i hi
  have h2 := fiveCliqueRepresentative_labels q j hj
  rw [he, h2] at h1
  exact Finset.singleton_inj.mp h1.symm

theorem fiveCliqueRepresentatives_card (q : Fin 5 → V) :
    (fiveCliqueRepresentatives G q).card = (fiveCliqueActiveLabels G q).card := by
  exact Finset.card_image_of_injOn (fiveCliqueRepresentative_injOn q)

theorem fiveCliqueActiveLabels_card_le_five (q : Fin 5 → V) :
    (fiveCliqueActiveLabels G q).card ≤ 5 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem fiveCliqueRepresentatives_outside (q : Fin 5 → V) :
    ∀ x ∈ fiveCliqueRepresentatives G q, x ∉ fiveCliqueSet q := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact fiveCliqueRepresentative_outside q i hi

theorem fiveCliqueRepresentatives_single (q : Fin 5 → V) :
    ∀ x ∈ fiveCliqueRepresentatives G q, (fiveCliqueLabels G q x).card = 1 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [fiveCliqueRepresentative_labels q i hi]
  simp

theorem fiveCliqueRepresentatives_distinct_labels (q : Fin 5 → V) :
    ∀ x ∈ fiveCliqueRepresentatives G q, ∀ y ∈ fiveCliqueRepresentatives G q, x ≠ y →
      fiveCliqueLabels G q x ≠ fiveCliqueLabels G q y := by
  intro x hx y hy hxy he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rw [fiveCliqueRepresentative_labels q i hi, fiveCliqueRepresentative_labels q j hj] at he
  exact hxy (congrArg (fiveCliqueRepresentative G q) (Finset.singleton_inj.mp he))

variable [DecidableRel G.Adj]

theorem fiveClique_full_open_packing
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (q : Fin 5 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x) :
    (δ - 5) * (fiveCliqueMulti G q).card +
      (δ - 1) * (fiveCliqueActiveLabels G q).card ≤ Fintype.card V - 5 := by
  have hh := fiveClique_selected_open_packing hcrit hr hn q hq hclique δ hdegree
    (fiveCliqueRepresentatives G q) (fiveCliqueRepresentatives_outside q)
    (fiveCliqueRepresentatives_single q) (fiveCliqueRepresentatives_distinct_labels q)
  rwa [fiveCliqueRepresentatives_card q] at hh

omit [Fintype V] in
theorem fiveClique_root_internal_neighbors_card (q : Fin 5 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) (i : Fin 5) :
    (packingNeighborsIn G (fiveCliqueSet q) (q i)).card = 4 := by
  rw [fiveClique_internal_neighbors_card q hq]
  have he : fiveCliqueLabels G q (q i) = (Finset.univ : Finset (Fin 5)).erase i := by
    ext j
    simp only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hij hji
      subst j
      exact G.loopless.irrefl _ hij
    · intro hji
      exact hclique i j hji.symm
  rw [he, Finset.card_erase_of_mem (Finset.mem_univ i)]
  norm_num

theorem fiveClique_missing_singleton_many_multi (q : Fin 5 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x)
    (hp : (fiveCliqueActiveLabels G q).card < 5) :
    δ - 4 ≤ (fiveCliqueMulti G q).card := by
  classical
  have hlt : (fiveCliqueActiveLabels G q).card <
      (Finset.univ : Finset (Fin 5)).card := by simpa using hp
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hnone : ¬ (fiveCliqueSingleGroup G q i).Nonempty := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsub : packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i) ⊆ fiveCliqueMulti G q := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    have hiL : i ∈ fiveCliqueLabels G q x := by
      simpa only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and]
        using hh.2.symm
    have hl : 2 ≤ (fiveCliqueLabels G q x).card := by
      by_contra hsmall
      have hle : (fiveCliqueLabels G q x).card ≤ 1 := by omega
      have he : fiveCliqueLabels G q x = {i} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hiL, fun j hj => Finset.card_le_one.mp hle j hj i hiL⟩
      apply hnone
      exact ⟨x, Finset.mem_filter.mpr ⟨hh.1, he⟩⟩
    exact Finset.mem_filter.mpr ⟨hh.1, hl⟩
  have hout : δ - 4 ≤ (packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i)).card :=
    packingNeighborsIn_compl_lower (fiveCliqueSet q) (q i) δ 4 (hdegree _)
      (fiveClique_root_internal_neighbors_card q hq hclique i).le
  exact hout.trans (Finset.card_le_card hsub)

end TaskH.Seven

#print axioms TaskH.Seven.fiveCliqueSingleGroup
#print axioms TaskH.Seven.fiveCliqueActiveLabels
#print axioms TaskH.Seven.fiveCliqueRepresentative
#print axioms TaskH.Seven.fiveCliqueRepresentatives
#print axioms TaskH.Seven.fiveCliqueRepresentative_mem
#print axioms TaskH.Seven.fiveCliqueRepresentative_labels
#print axioms TaskH.Seven.fiveCliqueRepresentative_outside
#print axioms TaskH.Seven.fiveCliqueRepresentative_injOn
#print axioms TaskH.Seven.fiveCliqueRepresentatives_card
#print axioms TaskH.Seven.fiveCliqueActiveLabels_card_le_five
#print axioms TaskH.Seven.fiveCliqueRepresentatives_outside
#print axioms TaskH.Seven.fiveCliqueRepresentatives_single
#print axioms TaskH.Seven.fiveCliqueRepresentatives_distinct_labels
#print axioms TaskH.Seven.fiveClique_full_open_packing
#print axioms TaskH.Seven.fiveClique_root_internal_neighbors_card
#print axioms TaskH.Seven.fiveClique_missing_singleton_many_multi
