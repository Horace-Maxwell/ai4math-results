import Research.TaskH.Seven.SevenK5CommonNeighbor
import Research.TaskH.Six.SixOpenNeighborhoodPacking

/-!
Five-clique labels and the actual open-neighborhood budget. The selected
singleton representatives in this helper are finite sets of real vertices;
applications must construct them from all nonempty label classes.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u}

noncomputable def fiveCliqueSet (q : Fin 5 → V) : Finset V := Finset.univ.image q

noncomputable def fiveCliqueLabels (G : SimpleGraph V) (q : Fin 5 → V) (x : V) :
    Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj x (q i))

noncomputable def fiveCliqueMulti [Fintype V] (G : SimpleGraph V) (q : Fin 5 → V) :
    Finset V := (fiveCliqueSet q)ᶜ.filter (fun x => 2 ≤ (fiveCliqueLabels G q x).card)

theorem fiveCliqueSet_card (q : Fin 5 → V) (hq : Function.Injective q) :
    (fiveCliqueSet q).card = 5 := by
  rw [fiveCliqueSet, Finset.card_image_of_injective _ hq]
  simp

theorem distinct_labels_have_distinct_roots (I J : Finset (Fin 5))
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
theorem fiveClique_internal_neighbors_card (q : Fin 5 → V)
    (hq : Function.Injective q) (x : V) :
    (packingNeighborsIn G (fiveCliqueSet q) x).card = (fiveCliqueLabels G q x).card := by
  have he : packingNeighborsIn G (fiveCliqueSet q) x =
      (fiveCliqueLabels G q x).image q := by
    ext y
    simp only [packingNeighborsIn, fiveCliqueSet, fiveCliqueLabels,
      Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, hxi⟩
      exact ⟨i, hxi, rfl⟩
    · rintro ⟨i, hxi, rfl⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
  rw [he, Finset.card_image_of_injective _ hq]

theorem fiveClique_selected_open_packing
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (q : Fin 5 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (δ : ℕ) (hdegree : ∀ x : V, δ ≤ G.degree x)
    (P : Finset V) (hPout : ∀ x ∈ P, x ∉ fiveCliqueSet q)
    (hPsingle : ∀ x ∈ P, (fiveCliqueLabels G q x).card = 1)
    (hPdistinct : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      fiveCliqueLabels G q x ≠ fiveCliqueLabels G q y) :
    (δ - 5) * (fiveCliqueMulti G q).card + (δ - 1) * P.card ≤
      Fintype.card V - 5 := by
  classical
  let M := fiveCliqueMulti G q
  let H := (fiveCliqueSet q)ᶜ
  have hMout : ∀ x ∈ M, x ∉ fiveCliqueSet q := by
    intro x hx
    exact Finset.mem_compl.mp (Finset.mem_filter.mp hx).1
  have hMlarge : ∀ x ∈ M, 2 ≤ (fiveCliqueLabels G q x).card := by
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
    have hxQ : x ∉ fiveCliqueSet q := by
      rcases Finset.mem_union.mp hx with hxM | hxP
      · exact hMout x hxM
      · exact hPout x hxP
    apply hxQ
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnonempty : ∀ x ∈ M ∪ P, (fiveCliqueLabels G q x).Nonempty := by
    intro x hx
    apply Finset.card_pos.mp
    rcases Finset.mem_union.mp hx with hxM | hxP
    · have hh := hMlarge x hxM
      omega
    · rw [hPsingle x hxP]
      decide
  have hlabels : ∀ x ∈ M ∪ P, ∀ y ∈ M ∪ P, x ≠ y →
      ∃ a b : Fin 5, a ≠ b ∧ G.Adj (q a) x ∧ G.Adj (q b) y := by
    intro x hx y hy hxy
    have hlarge : 2 ≤ (fiveCliqueLabels G q x).card ∨
        2 ≤ (fiveCliqueLabels G q y).card ∨
        fiveCliqueLabels G q x ≠ fiveCliqueLabels G q y := by
      rcases Finset.mem_union.mp hx with hxM | hxP
      · exact Or.inl (hMlarge x hxM)
      · rcases Finset.mem_union.mp hy with hyM | hyP
        · exact Or.inr (Or.inl (hMlarge y hyM))
        · exact Or.inr (Or.inr (hPdistinct x hxP y hyP hxy))
    obtain ⟨a, ha, b, hb, hab⟩ := distinct_labels_have_distinct_roots
      (fiveCliqueLabels G q x) (fiveCliqueLabels G q y)
      (hnonempty x hx) (hnonempty y hy) hlarge
    have hax : G.Adj x (q a) := by
      simpa only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have hby : G.Adj y (q b) := by
      simpa only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    exact ⟨a, b, hab, hax.symm, hby.symm⟩
  have hcommon : ∀ z ∈ H, ∀ x ∈ M ∪ P, ∀ y ∈ M ∪ P,
      G.Adj x z → G.Adj y z → x = y := by
    intro z hz x hx y hy hxz hyz
    have hzq : ∀ i, q i ≠ z := by
      intro i he
      have hzQ : z ∉ fiveCliqueSet q := Finset.mem_compl.mp hz
      apply hzQ
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    by_cases hxy : x = y
    · exact hxy
    · obtain ⟨a, b, hab, hax, hby⟩ := hlabels x hx y hy hxy
      exact five_clique_distinct_roots_common_neighbor_unique hcrit hr hn q hq hclique
        x y z (hout x hx) (hout y hy) hzq a b hab hax hby hxz hyz
  have hM : ∀ x ∈ M, δ - 5 ≤ (packingNeighborsIn G H x).card := by
    intro x _hx
    have hin : (packingNeighborsIn G (fiveCliqueSet q) x).card ≤ 5 := by
      exact (Finset.card_le_card (packingNeighborsIn_subset (G := G) _ _)).trans
        (fiveCliqueSet_card q hq).le
    exact packingNeighborsIn_compl_lower (fiveCliqueSet q) x δ 5 (hdegree x) hin
  have hP : ∀ x ∈ P, δ - 1 ≤ (packingNeighborsIn G H x).card := by
    intro x hx
    have hin : (packingNeighborsIn G (fiveCliqueSet q) x).card ≤ 1 := by
      rw [fiveClique_internal_neighbors_card q hq, hPsingle x hx]
    exact packingNeighborsIn_compl_lower (fiveCliqueSet q) x δ 1 (hdegree x) hin
  have hh := actual_open_neighborhood_two_class_packing M P H (δ - 5) (δ - 1)
    hdisjoint hM hP hcommon
  have hcard : H.card = Fintype.card V - 5 := by
    have hp := Finset.card_add_card_compl (fiveCliqueSet q)
    rw [fiveCliqueSet_card q hq] at hp
    change 5 + H.card = Fintype.card V at hp
    omega
  rw [hcard] at hh
  exact hh

end TaskH.Seven

#print axioms TaskH.Seven.fiveCliqueSet
#print axioms TaskH.Seven.fiveCliqueLabels
#print axioms TaskH.Seven.fiveCliqueMulti
#print axioms TaskH.Seven.fiveCliqueSet_card
#print axioms TaskH.Seven.distinct_labels_have_distinct_roots
#print axioms TaskH.Seven.fiveClique_internal_neighbors_card
#print axioms TaskH.Seven.fiveClique_selected_open_packing
