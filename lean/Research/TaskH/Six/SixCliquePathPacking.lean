import Research.TaskH.Six.CycleSix

/-!
Actual deleted-coloring transport for a four-clique joined by a three-point
external path. Two genuine hexagons force seven differently colored points
in a six-coloring. The graph's original criticality supplies the coloring.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem rainbow_hexagon_colors_injective
    (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (f : Fin 6 → V) (hf : IsHexagon G f) (hfw : ∀ i, f i ≠ w) :
    Function.Injective (fun i => c ⟨f i, hfw i⟩) := by
  let p := hexagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hp : p.IsCycle := hexagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hmem : ∀ i, f i ∈ p.support := by
    intro i
    fin_cases i <;> simp [p, hexagonWalk, Walk.support_cons]
  intro i j hij
  apply hf.1
  exact congrArg Subtype.val
    (hr w c p hp (by rfl) ⟨f i, hfw i⟩ ⟨f j, hfw j⟩ (hmem i) (hmem j) hij)

def fourCliquePathHexagon (q : Fin 4 → V) (t : Fin 3 → V)
    (s : Fin 4) : Fin 6 → V := ![q 0, t 0, t 1, t 2, q 1, q s]

theorem fourCliquePathHexagon_injective
    (q : Fin 4 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (s : Fin 4) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Function.Injective (fourCliquePathHexagon q t s) := by
  have htq : ∀ j i, t j ≠ q i := fun j i he => hqt i j he.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [fourCliquePathHexagon, hq.eq_iff, ht.eq_iff]

theorem fourCliquePathHexagon_isHexagon
    (q : Fin 4 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1))
    (s : Fin 4) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    IsHexagon G (fourCliquePathHexagon q t s) := by
  refine ⟨fourCliquePathHexagon_injective q t hq ht hqt s hs0 hs1,
    hleft, h01, h12, hright, hclique 1 s hs1.symm, hclique s 0 hs0⟩

theorem four_clique_path_coloring_incompatible
    (hr : RainbowSixCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (q : Fin 4 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hqw : ∀ i, q i ≠ w) (htw : ∀ j, t j ≠ w)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1)) : False := by
  classical
  let f2 := fourCliquePathHexagon q t 2
  let f3 := fourCliquePathHexagon q t 3
  have hf2 : IsHexagon G f2 := fourCliquePathHexagon_isHexagon q t hq ht hqt
    hclique hleft h01 h12 hright 2 (by decide) (by decide)
  have hf3 : IsHexagon G f3 := fourCliquePathHexagon_isHexagon q t hq ht hqt
    hclique hleft h01 h12 hright 3 (by decide) (by decide)
  have h2w : ∀ i, f2 i ≠ w := by
    intro i
    fin_cases i <;> simp [f2, fourCliquePathHexagon, hqw, htw]
  have h3w : ∀ i, f3 i ≠ w := by
    intro i
    fin_cases i <;> simp [f3, fourCliquePathHexagon, hqw, htw]
  let g2 : Fin 6 → Fin 6 := fun i => c ⟨f2 i, h2w i⟩
  let g3 : Fin 6 → Fin 6 := fun i => c ⟨f3 i, h3w i⟩
  have hi2 : Function.Injective g2 := rainbow_hexagon_colors_injective hr w c f2 hf2 h2w
  have hi3 : Function.Injective g3 := rainbow_hexagon_colors_injective hr w c f3 hf3 h3w
  let qc : Fin 4 → Fin 6 := fun i => c ⟨q i, hqw i⟩
  let tc : Fin 3 → Fin 6 := fun i => c ⟨t i, htw i⟩
  have hqi : Function.Injective qc := by
    intro i j hij
    by_contra hne
    have ha : (G.induce {x | x ≠ w}).Adj ⟨q i, hqw i⟩ ⟨q j, hqw j⟩ :=
      hclique i j hne
    exact (c.valid ha) hij
  let idx : Fin 3 → Fin 6 := ![1, 2, 3]
  have hidx : Function.Injective idx := by decide +kernel
  have he2 : g2 ∘ idx = tc := by
    funext i
    fin_cases i <;> rfl
  have he3 : g3 ∘ idx = tc := by
    funext i
    fin_cases i <;> rfl
  have hti : Function.Injective tc := by
    rw [← he2]
    exact hi2.comp hidx
  have hcross : ∀ i j, qc i ≠ tc j := by
    intro i j hij
    fin_cases i
    · have he : g2 0 = g2 (idx j) := by
        change qc 0 = (g2 ∘ idx) j
        rw [he2]
        exact hij
      have hh := hi2 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g2 4 = g2 (idx j) := by
        change qc 1 = (g2 ∘ idx) j
        rw [he2]
        exact hij
      have hh := hi2 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g2 5 = g2 (idx j) := by
        change qc 2 = (g2 ∘ idx) j
        rw [he2]
        exact hij
      have hh := hi2 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g3 5 = g3 (idx j) := by
        change qc 3 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
  have hseven : Function.Injective (Fin.append qc tc) :=
    Fin.append_injective_iff.mpr ⟨hqi, hti, hcross⟩
  have hcard := Fintype.card_le_of_injective (Fin.append qc tc) hseven
  norm_num at hcard

theorem critical_no_four_clique_external_three_path [Fintype V]
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V)
    (q : Fin 4 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1)) : False := by
  classical
  let S := (Finset.univ.image q) ∪ (Finset.univ.image t)
  have hqcard : (Finset.univ.image q).card ≤ 4 := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := q)
  have htcard : (Finset.univ.image t).card ≤ 3 := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := t)
  have hS : S.card ≤ 7 := by
    have hh := Finset.card_union_le (Finset.univ.image q) (Finset.univ.image t)
    change ((Finset.univ.image q) ∪ (Finset.univ.image t)).card ≤ 7
    omega
  have hlt : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hw
    rw [← he]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have htw : ∀ j, t j ≠ w := by
    intro j he
    apply hw
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  exact four_clique_path_coloring_incompatible hr w c q t hq ht hqt hqw htw
    hclique hleft h01 h12 hright

end TaskH.Six

#print axioms TaskH.Six.rainbow_hexagon_colors_injective
#print axioms TaskH.Six.fourCliquePathHexagon
#print axioms TaskH.Six.fourCliquePathHexagon_injective
#print axioms TaskH.Six.fourCliquePathHexagon_isHexagon
#print axioms TaskH.Six.four_clique_path_coloring_incompatible
#print axioms TaskH.Six.critical_no_four_clique_external_three_path
