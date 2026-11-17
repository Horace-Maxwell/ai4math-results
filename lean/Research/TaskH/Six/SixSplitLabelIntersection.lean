import Research.TaskH.Six.SixRainbowHexagonCollision

/-! Real rainbow hexagons constrain the labels of same-color four-leaf attachments. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

theorem four_label_overlap_has_three_distinct
    (I J : Finset (Fin 4)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card)
    (hinter : ¬ Disjoint I J) (hbad : ¬ (I = J ∧ I.card = 2)) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ l ∈ J,
      j ∈ J ∧ i ≠ j ∧ j ≠ l ∧ i ≠ l := by
  revert I J
  decide +kernel

noncomputable def fourLeafLabels {V : Type u} (G : SimpleGraph V)
    (p : Fin 4 → V) (z : V) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => G.Adj z (p i))

theorem mem_fourLeafLabels_iff {V : Type u} {G : SimpleGraph V}
    (p : Fin 4 → V) (z : V) (i : Fin 4) :
    i ∈ fourLeafLabels G p z ↔ G.Adj z (p i) := by
  simp [fourLeafLabels]

theorem same_color_four_leaf_labels_intersection
    {V : Type u} {G : SimpleGraph V}
    (hr : RainbowSixCycles G) (v a : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : Fin 4 → V) (hp : Function.Injective p)
    (hva : G.Adj v a) (hvp : ∀ i, G.Adj v (p i))
    (hap : ∀ i, G.Adj a (p i)) (x y : V)
    (hx : x ≠ v ∧ ¬ G.Adj v x) (hy : y ≠ v ∧ ¬ G.Adj v y)
    (hxy : x ≠ y) (hcolor : c ⟨x, hx.1⟩ = c ⟨y, hy.1⟩)
    (hLx : 2 ≤ (fourLeafLabels G p x).card)
    (hLy : 2 ≤ (fourLeafLabels G p y).card) :
    Disjoint (fourLeafLabels G p x) (fourLeafLabels G p y) ∨
      (fourLeafLabels G p x = fourLeafLabels G p y ∧
        (fourLeafLabels G p x).card = 2) := by
  classical
  by_cases hd : Disjoint (fourLeafLabels G p x) (fourLeafLabels G p y)
  · exact Or.inl hd
  by_cases he : fourLeafLabels G p x = fourLeafLabels G p y ∧
      (fourLeafLabels G p x).card = 2
  · exact Or.inr he
  obtain ⟨i, hi, j, hj, l, hl, hj', hij, hjl, hil⟩ :=
    four_label_overlap_has_three_distinct (fourLeafLabels G p x)
      (fourLeafLabels G p y) hLx hLy hd he
  have hxi := (mem_fourLeafLabels_iff p x i).mp hi
  have hxj := (mem_fourLeafLabels_iff p x j).mp hj
  have hyj := (mem_fourLeafLabels_iff p y j).mp hj'
  have hyl := (mem_fourLeafLabels_iff p y l).mp hl
  have hax : a ≠ x := by intro he; exact hx.2 (by simpa only [← he] using hva)
  have hay : a ≠ y := by intro he; exact hy.2 (by simpa only [← he] using hva)
  have hpx : ∀ k, p k ≠ x := by
    intro k he
    exact hx.2 (by simpa only [← he] using hvp k)
  have hpy : ∀ k, p k ≠ y := by
    intro k he
    exact hy.2 (by simpa only [← he] using hvp k)
  have hap_ne : ∀ k, a ≠ p k := fun k => (hap k).ne
  have hpa_ne : ∀ k, p k ≠ a := fun k => (hap k).ne.symm
  let f : Fin 6 → V := ![a, p i, x, p j, y, p l]
  have hfi : Function.Injective f := by
    intro b d hbd
    fin_cases b <;> fin_cases d <;> simp_all [f, hp.eq_iff]
  have hf : IsHexagon G f :=
    ⟨hfi, hap i, hxi.symm, hxj, hyj.symm, hyl, (hap l).symm⟩
  exact False.elim (rainbow_hexagon_same_color_impossible hr v c f hf x y
    hx.1 hy.1 hxy ⟨2, rfl⟩ ⟨4, rfl⟩ hcolor)

end TaskH.Six

#print axioms TaskH.Six.four_label_overlap_has_three_distinct
#print axioms TaskH.Six.fourLeafLabels
#print axioms TaskH.Six.mem_fourLeafLabels_iff
#print axioms TaskH.Six.same_color_four_leaf_labels_intersection
