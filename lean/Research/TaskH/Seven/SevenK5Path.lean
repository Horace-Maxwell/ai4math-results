import Research.TaskH.Seven.SevenCliqueRainbow
import Research.TaskH.Critical

/-!
Two actual seven-cycles transport the original deleted-coloring R to the
K5 outside-path restriction. The forbidden external path has three outside
vertices (two H-edges), attached to distinct clique vertices. Empty-label
vertices are not removed or assumed absent.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V}

def fiveCliquePathHeptagon (q : Fin 5 → V) (t : Fin 3 → V)
    (s : Fin 5) : Fin 7 → V := ![q 0, t 0, t 1, t 2, q 1, q 2, q s]

theorem fiveCliquePathHeptagon_injective
    (q : Fin 5 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (s : Fin 5)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs2 : s ≠ 2) :
    Function.Injective (fiveCliquePathHeptagon q t s) := by
  have htq : ∀ j i, t j ≠ q i := fun j i he => hqt i j he.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [fiveCliquePathHeptagon, hq.eq_iff, ht.eq_iff]

theorem fiveCliquePathHeptagon_isHeptagon
    (q : Fin 5 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1))
    (s : Fin 5) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hs2 : s ≠ 2) :
    IsHeptagon G (fiveCliquePathHeptagon q t s) := by
  refine ⟨fiveCliquePathHeptagon_injective q t hq ht hqt s hs0 hs1 hs2,
    hleft, h01, h12, hright, hclique 1 2 (by decide),
    hclique 2 s hs2.symm, hclique s 0 hs0⟩

theorem five_clique_path_coloring_incompatible
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (q : Fin 5 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hqw : ∀ i, q i ≠ w) (htw : ∀ j, t j ≠ w)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1)) : False := by
  classical
  let f3 := fiveCliquePathHeptagon q t 3
  let f4 := fiveCliquePathHeptagon q t 4
  have hf3 : IsHeptagon G f3 := fiveCliquePathHeptagon_isHeptagon q t hq ht hqt
    hclique hleft h01 h12 hright 3 (by decide) (by decide) (by decide)
  have hf4 : IsHeptagon G f4 := fiveCliquePathHeptagon_isHeptagon q t hq ht hqt
    hclique hleft h01 h12 hright 4 (by decide) (by decide) (by decide)
  have h3w : ∀ i, f3 i ≠ w := by
    intro i
    fin_cases i <;> simp [f3, fiveCliquePathHeptagon, hqw, htw]
  have h4w : ∀ i, f4 i ≠ w := by
    intro i
    fin_cases i <;> simp [f4, fiveCliquePathHeptagon, hqw, htw]
  let g3 : Fin 7 → Fin 7 := fun i => c ⟨f3 i, h3w i⟩
  let g4 : Fin 7 → Fin 7 := fun i => c ⟨f4 i, h4w i⟩
  have hi3 : Function.Injective g3 := rainbow_heptagon_colors_injective hr w c f3 hf3 h3w
  have hi4 : Function.Injective g4 := rainbow_heptagon_colors_injective hr w c f4 hf4 h4w
  let qc : Fin 5 → Fin 7 := fun i => c ⟨q i, hqw i⟩
  let tc : Fin 3 → Fin 7 := fun i => c ⟨t i, htw i⟩
  have hqi : Function.Injective qc := by
    intro i j hij
    by_contra hne
    have ha : (G.induce {x | x ≠ w}).Adj ⟨q i, hqw i⟩ ⟨q j, hqw j⟩ :=
      hclique i j hne
    exact (c.valid ha) hij
  let idx : Fin 3 → Fin 7 := ![1, 2, 3]
  have hidx : Function.Injective idx := by decide +kernel
  have he3 : g3 ∘ idx = tc := by
    funext i
    fin_cases i <;> rfl
  have he4 : g4 ∘ idx = tc := by
    funext i
    fin_cases i <;> rfl
  have hti : Function.Injective tc := by
    rw [← he3]
    exact hi3.comp hidx
  have hcross : ∀ i j, qc i ≠ tc j := by
    intro i j hij
    fin_cases i
    · have he : g3 0 = g3 (idx j) := by
        change qc 0 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g3 4 = g3 (idx j) := by
        change qc 1 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g3 5 = g3 (idx j) := by
        change qc 2 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g3 6 = g3 (idx j) := by
        change qc 3 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g4 6 = g4 (idx j) := by
        change qc 4 = (g4 ∘ idx) j
        rw [he4]
        exact hij
      have hh := hi4 he
      fin_cases j <;> norm_num [idx] at hh
  have height : Function.Injective (Fin.append qc tc) :=
    Fin.append_injective_iff.mpr ⟨hqi, hti, hcross⟩
  have hcard := Fintype.card_le_of_injective (Fin.append qc tc) height
  norm_num at hcard

theorem critical_no_five_clique_external_three_path [Fintype V]
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q 1)) : False := by
  classical
  let S := (Finset.univ.image q) ∪ (Finset.univ.image t)
  have hqcard : (Finset.univ.image q).card ≤ 5 := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := q)
  have htcard : (Finset.univ.image t).card ≤ 3 := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := t)
  have hS : S.card ≤ 8 := by
    have hh := Finset.card_union_le (Finset.univ.image q) (Finset.univ.image t)
    change ((Finset.univ.image q) ∪ (Finset.univ.image t)).card ≤ 8
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
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit w
  exact five_clique_path_coloring_incompatible hr w c q t hq ht hqt hqw htw
    hclique hleft h01 h12 hright

end TaskH.Seven

#print axioms TaskH.Seven.fiveCliquePathHeptagon
#print axioms TaskH.Seven.fiveCliquePathHeptagon_injective
#print axioms TaskH.Seven.fiveCliquePathHeptagon_isHeptagon
#print axioms TaskH.Seven.five_clique_path_coloring_incompatible
#print axioms TaskH.Seven.critical_no_five_clique_external_three_path
