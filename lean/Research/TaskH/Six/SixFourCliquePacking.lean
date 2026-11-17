import Research.TaskH.Six.SixCliqueCommonNeighbors

/-!
Four-clique labels and the actual open-neighborhood budget. The selected
singleton representatives in this helper are finite sets of real vertices;
applications must construct them from all nonempty label classes.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u}

noncomputable def fourCliqueSet (q : Fin 4 → V) : Finset V := Finset.univ.image q

noncomputable def fourCliqueLabels (G : SimpleGraph V) (q : Fin 4 → V) (x : V) :
    Finset (Fin 4) := Finset.univ.filter (fun i => G.Adj x (q i))

noncomputable def fourCliqueMulti [Fintype V] (G : SimpleGraph V) (q : Fin 4 → V) :
    Finset V := (fourCliqueSet q)ᶜ.filter (fun x => 2 ≤ (fourCliqueLabels G q x).card)

theorem fourCliqueSet_card (q : Fin 4 → V) (hq : Function.Injective q) :
    (fourCliqueSet q).card = 4 := by
  rw [fourCliqueSet, Finset.card_image_of_injective _ hq]
  simp

theorem distinct_labels_have_distinct_roots (I J : Finset (Fin 4))
    (hI : I.Nonempty) (hJ : J.Nonempty)
    (hlarge : 2 ≤ I.card ∨ 2 ≤ J.card ∨ I ≠ J) :
    ∃ a ∈ I, ∃ b ∈ J, a ≠ b := by
  classical
  by_contra hno
  have heq : ∀ a ∈ I, ∀ b ∈ J, a = b := by simpa using hno
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb⟩ := hJ
  have hIc : I.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (heq x hx b hb).trans (heq y hy b hb).symm)
  have hJc : J.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (heq a ha x hx).symm.trans (heq a ha y hy))
  have hIJ : I = J := by
    ext z
    constructor
    · intro hz
      rw [heq z hz b hb]
      exact hb
    · intro hz
      rw [← heq a ha z hz]
      exact ha
  rcases hlarge with h | h | h
  · omega
  · omega
  · exact h hIJ

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem fourClique_internal_neighbors_card (q : Fin 4 → V)
    (hq : Function.Injective q) (x : V) :
    (packingNeighborsIn G (fourCliqueSet q) x).card = (fourCliqueLabels G q x).card := by
  have he : packingNeighborsIn G (fourCliqueSet q) x =
      (fourCliqueLabels G q x).image q := by
    ext y
    simp only [packingNeighborsIn, fourCliqueSet, fourCliqueLabels,
      Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hxi⟩
      exact ⟨i, hxi, rfl⟩
    · rintro ⟨i, hxi, rfl⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
  rw [he, Finset.card_image_of_injective _ hq]

theorem fourClique_selected_open_packing
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x)
    (P : Finset V) (hPout : ∀ x ∈ P, x ∉ fourCliqueSet q)
    (hPsingle : ∀ x ∈ P, (fourCliqueLabels G q x).card = 1)
    (hPdistinct : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      fourCliqueLabels G q x ≠ fourCliqueLabels G q y) :
    (δ - 4) * (fourCliqueMulti G q).card + (δ - 1) * P.card ≤
      Fintype.card V - 4 := by
  classical
  let M := fourCliqueMulti G q
  let H := (fourCliqueSet q)ᶜ
  have hMout : ∀ x ∈ M, x ∉ fourCliqueSet q := by
    intro x hx
    exact Finset.mem_compl.mp (Finset.mem_filter.mp hx).1
  have hMlarge : ∀ x ∈ M, 2 ≤ (fourCliqueLabels G q x).card := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hdisjoint : Disjoint M P := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h0 := hMlarge x hx
    have h1 := hPsingle x hy
    omega
  have hout : ∀ x ∈ M ∪ P, ∀ i, q i ≠ x := by
    intro x hx i he
    have hxQ : x ∉ fourCliqueSet q := by
      rcases Finset.mem_union.mp hx with hxM | hxP
      · exact hMout x hxM
      · exact hPout x hxP
    apply hxQ
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnonempty : ∀ x ∈ M ∪ P, (fourCliqueLabels G q x).Nonempty := by
    intro x hx
    apply Finset.card_pos.mp
    rcases Finset.mem_union.mp hx with hxM | hxP
    · have hh := hMlarge x hxM
      omega
    · rw [hPsingle x hxP]
      decide
  have hlabels : ∀ x ∈ M ∪ P, ∀ y ∈ M ∪ P, x ≠ y →
      ∃ a b : Fin 4, a ≠ b ∧ G.Adj (q a) x ∧ G.Adj (q b) y := by
    intro x hx y hy hxy
    have hlarge : 2 ≤ (fourCliqueLabels G q x).card ∨
        2 ≤ (fourCliqueLabels G q y).card ∨
        fourCliqueLabels G q x ≠ fourCliqueLabels G q y := by
      rcases Finset.mem_union.mp hx with hxM | hxP
      · exact Or.inl (hMlarge x hxM)
      · rcases Finset.mem_union.mp hy with hyM | hyP
        · exact Or.inr (Or.inl (hMlarge y hyM))
        · exact Or.inr (Or.inr (hPdistinct x hxP y hyP hxy))
    obtain ⟨a, ha, b, hb, hab⟩ := distinct_labels_have_distinct_roots
      (fourCliqueLabels G q x) (fourCliqueLabels G q y)
      (hnonempty x hx) (hnonempty y hy) hlarge
    have hax : G.Adj x (q a) := by
      simpa only [fourCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have hby : G.Adj y (q b) := by
      simpa only [fourCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    exact ⟨a, b, hab, hax.symm, hby.symm⟩
  have hcommon : ∀ z ∈ H, ∀ x ∈ M ∪ P, ∀ y ∈ M ∪ P,
      G.Adj x z → G.Adj y z → x = y := by
    intro z hz x hx y hy hxz hyz
    have hzq : ∀ i, q i ≠ z := by
      intro i he
      have hzQ : z ∉ fourCliqueSet q := Finset.mem_compl.mp hz
      apply hzQ
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact four_clique_selected_attachment_common_neighbor_unique hcrit hr hn q hq
      hclique (M ∪ P) hout hlabels z hzq x hx y hy hxz hyz
  have hM : ∀ x ∈ M, δ - 4 ≤ (packingNeighborsIn G H x).card := by
    intro x _hx
    have hin : (packingNeighborsIn G (fourCliqueSet q) x).card ≤ 4 := by
      exact (Finset.card_le_card (packingNeighborsIn_subset (G := G) _ _)).trans
        (fourCliqueSet_card q hq).le
    exact packingNeighborsIn_compl_lower (fourCliqueSet q) x δ 4 (hdegree x) hin
  have hP : ∀ x ∈ P, δ - 1 ≤ (packingNeighborsIn G H x).card := by
    intro x hx
    have hin : (packingNeighborsIn G (fourCliqueSet q) x).card ≤ 1 := by
      rw [fourClique_internal_neighbors_card q hq, hPsingle x hx]
    exact packingNeighborsIn_compl_lower (fourCliqueSet q) x δ 1 (hdegree x) hin
  have hh := actual_open_neighborhood_two_class_packing M P H (δ - 4) (δ - 1)
    hdisjoint hM hP hcommon
  have hcard : H.card = Fintype.card V - 4 := by
    have hp := Finset.card_add_card_compl (fourCliqueSet q)
    rw [fourCliqueSet_card q hq] at hp
    change 4 + H.card = Fintype.card V at hp
    omega
  rw [hcard] at hh
  exact hh

end TaskH.Six

#print axioms TaskH.Six.fourCliqueSet
#print axioms TaskH.Six.fourCliqueLabels
#print axioms TaskH.Six.fourCliqueMulti
#print axioms TaskH.Six.fourCliqueSet_card
#print axioms TaskH.Six.distinct_labels_have_distinct_roots
#print axioms TaskH.Six.fourClique_internal_neighbors_card
#print axioms TaskH.Six.fourClique_selected_open_packing
