import Research.TaskH.Seven.SevenK5PackingCompatibility

/-! Three pairwise compatible actual attachment labels would require three
colors outside the same five clique colors in one proper seven-coloring. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem critical_five_clique_no_compatible_triangle
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, x ≠ q i) (hy : ∀ i, y ≠ q i) (hz : ∀ i, z ≠ q i)
    (hxL : 2 ≤ (fiveCliqueLabels G q x).card)
    (hyL : 2 ≤ (fiveCliqueLabels G q y).card)
    (hzL : 2 ≤ (fiveCliqueLabels G q z).card)
    (hxyL : 4 ≤ (fiveCliqueLabels G q x ∪ fiveCliqueLabels G q y).card)
    (hxzL : 4 ≤ (fiveCliqueLabels G q x ∪ fiveCliqueLabels G q z).card)
    (hyzL : 4 ≤ (fiveCliqueLabels G q y ∪ fiveCliqueLabels G q z).card) : False := by
  classical
  let S := fiveCliqueSet q ∪ {x, y, z}
  have hQ : (fiveCliqueSet q).card = 5 := fiveCliqueSet_card q hq
  have hS : S.card ≤ 8 := by
    have hh := Finset.card_union_le (fiveCliqueSet q) {x, y, z}
    have hh' := (Finset.card_le_three : ({x, y, z} : Finset V).card ≤ 3)
    change (fiveCliqueSet q ∪ {x, y, z}).card ≤ 8
    omega
  have hlt : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _hw, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hw
    rw [← he]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hxw : x ≠ w := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hyw : y ≠ w := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hzw : z ≠ w := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit w
  have hxyc := five_clique_compatible_color_constraints hr w c q hq hclique hqw
    x y hxw hyw hxy hx hy hxL hyL hxyL
  have hxzc := five_clique_compatible_color_constraints hr w c q hq hclique hqw
    x z hxw hzw hxz hx hz hxL hzL hxzL
  have hyzc := five_clique_compatible_color_constraints hr w c q hq hclique hqw
    y z hyw hzw hyz hy hz hyL hzL hyzL
  let qc : Fin 5 → Fin 7 := fun i => c ⟨q i, hqw i⟩
  let tc : Fin 3 → Fin 7 := ![c ⟨x, hxw⟩, c ⟨y, hyw⟩, c ⟨z, hzw⟩]
  have hqi : Function.Injective qc := by
    intro i j hc
    by_contra hij
    have hadj : (G.induce {a | a ≠ w}).Adj ⟨q i, hqw i⟩ ⟨q j, hqw j⟩ :=
      hclique i j hij
    exact (c.valid hadj) hc
  have hti : Function.Injective tc := by
    intro i j he
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hxyc.1 he)
      | exact False.elim (hxyc.1 he.symm)
      | exact False.elim (hxzc.1 he)
      | exact False.elim (hxzc.1 he.symm)
      | exact False.elim (hyzc.1 he)
      | exact False.elim (hyzc.1 he.symm)
  have hcross : ∀ i j, qc i ≠ tc j := by
    intro i j
    fin_cases j
    · exact Ne.symm (hxyc.2.1 i)
    · exact Ne.symm (hxyc.2.2 i)
    · exact Ne.symm (hxzc.2.2 i)
  have hinj : Function.Injective (Fin.append qc tc) :=
    Fin.append_injective_iff.mpr ⟨hqi, hti, hcross⟩
  have hcard := Fintype.card_le_of_injective (Fin.append qc tc) hinj
  norm_num at hcard

end TaskH.Seven
#print axioms TaskH.Seven.critical_five_clique_no_compatible_triangle
