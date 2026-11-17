import Research.TaskH.Seven.SevenK5PackingTriangle

/-! In an actual multi-label class with at least three vertices, at most
one label has size at least four. This gives total label incidence ≤3r+2. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem fiveCliqueMulti_outside (q : Fin 5 → V) (x : V)
    (hx : x ∈ fiveCliqueMulti G q) : ∀ i, x ≠ q i := by
  intro i he
  have hout := Finset.mem_compl.mp (Finset.mem_filter.mp hx).1
  apply hout
  rw [he]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem fiveCliqueMulti_label_card_ge_two (q : Fin 5 → V) (x : V)
    (hx : x ∈ fiveCliqueMulti G q) : 2 ≤ (fiveCliqueLabels G q x).card :=
  (Finset.mem_filter.mp hx).2

theorem fiveClique_heavy_label_unique
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hM : 3 ≤ (fiveCliqueMulti G q).card)
    (x y : V) (hx : x ∈ fiveCliqueMulti G q) (hy : y ∈ fiveCliqueMulti G q)
    (hx4 : 4 ≤ (fiveCliqueLabels G q x).card)
    (hy4 : 4 ≤ (fiveCliqueLabels G q y).card) : x = y := by
  classical
  by_contra hxy
  have hlt : ({x, y} : Finset V).card < (fiveCliqueMulti G q).card :=
    lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨z, hz, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hxz : x ≠ z := by
    intro he
    apply hznot
    exact Finset.mem_insert.mpr (Or.inl he.symm)
  have hyz : y ≠ z := by
    intro he
    apply hznot
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he.symm))
  have hxyL : 4 ≤ (fiveCliqueLabels G q x ∪ fiveCliqueLabels G q y).card :=
    hx4.trans (Finset.card_le_card Finset.subset_union_left)
  have hxzL : 4 ≤ (fiveCliqueLabels G q x ∪ fiveCliqueLabels G q z).card :=
    hx4.trans (Finset.card_le_card Finset.subset_union_left)
  have hyzL : 4 ≤ (fiveCliqueLabels G q y ∪ fiveCliqueLabels G q z).card :=
    hy4.trans (Finset.card_le_card Finset.subset_union_left)
  exact critical_five_clique_no_compatible_triangle hcrit hr hn9 q hq hclique
    x y z hxy hxz hyz (fiveCliqueMulti_outside q x hx)
    (fiveCliqueMulti_outside q y hy) (fiveCliqueMulti_outside q z hz)
    (fiveCliqueMulti_label_card_ge_two q x hx)
    (fiveCliqueMulti_label_card_ge_two q y hy)
    (fiveCliqueMulti_label_card_ge_two q z hz) hxyL hxzL hyzL

theorem fiveClique_multi_label_incidence_le
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hM : 3 ≤ (fiveCliqueMulti G q).card) :
    (∑ x ∈ fiveCliqueMulti G q, (fiveCliqueLabels G q x).card) ≤
      3 * (fiveCliqueMulti G q).card + 2 := by
  classical
  let M := fiveCliqueMulti G q
  let T := M.filter (fun x => 4 ≤ (fiveCliqueLabels G q x).card)
  have hT : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact fiveClique_heavy_label_unique hcrit hr hn9 q hq hclique hM x y
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hrow : ∀ x ∈ M, (fiveCliqueLabels G q x).card ≤
      3 + 2 * (if 4 ≤ (fiveCliqueLabels G q x).card then 1 else 0) := by
    intro x _hx
    have h5 : (fiveCliqueLabels G q x).card ≤ 5 :=
      (Finset.card_le_univ _).trans (by simp)
    split_ifs <;> omega
  have hones : (∑ x ∈ M, if 4 ≤ (fiveCliqueLabels G q x).card then 1 else 0) =
      T.card := by
    change _ = (M.filter (fun x => 4 ≤ (fiveCliqueLabels G q x).card)).card
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ ≤ ∑ x ∈ M, (3 + 2 * (if 4 ≤ (fiveCliqueLabels G q x).card then 1 else 0)) :=
      Finset.sum_le_sum hrow
    _ = 3 * M.card + 2 * T.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hones]
      simp [Nat.mul_comm]
    _ ≤ 3 * M.card + 2 := by omega

end TaskH.Seven
#print axioms TaskH.Seven.fiveCliqueMulti_outside
#print axioms TaskH.Seven.fiveCliqueMulti_label_card_ge_two
#print axioms TaskH.Seven.fiveClique_heavy_label_unique
#print axioms TaskH.Seven.fiveClique_multi_label_incidence_le
