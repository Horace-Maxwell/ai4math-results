import Research.TaskH.Seven.SevenCliqueRainbow
import Research.TaskH.Critical

/-!
An actual four-clique joined by a four-point outside path would force eight
colors into seven. This supplies the length-three H-path restriction used in
the K5 packing, without assuming any outside attachment coverage.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V}

def fourCliqueLongHeptagon (q : Fin 4 → V) (t : Fin 4 → V)
    (s : Fin 4) : Fin 7 → V := ![q 0, t 0, t 1, t 2, t 3, q 1, q s]

theorem fourCliqueLongHeptagon_injective
    (q : Fin 4 → V) (t : Fin 4 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (s : Fin 4) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Function.Injective (fourCliqueLongHeptagon q t s) := by
  have htq : ∀ j i, t j ≠ q i := fun j i he => hqt i j he.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [fourCliqueLongHeptagon, hq.eq_iff, ht.eq_iff]

theorem fourCliqueLongHeptagon_isHeptagon
    (q : Fin 4 → V) (t : Fin 4 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (h23 : G.Adj (t 2) (t 3))
    (hright : G.Adj (t 3) (q 1))
    (s : Fin 4) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    IsHeptagon G (fourCliqueLongHeptagon q t s) := by
  refine ⟨fourCliqueLongHeptagon_injective q t hq ht hqt s hs0 hs1,
    hleft, h01, h12, h23, hright, hclique 1 s hs1.symm, hclique s 0 hs0⟩

theorem four_clique_long_path_coloring_incompatible
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 7))
    (q : Fin 4 → V) (t : Fin 4 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hqw : ∀ i, q i ≠ w) (htw : ∀ j, t j ≠ w)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (h23 : G.Adj (t 2) (t 3))
    (hright : G.Adj (t 3) (q 1)) : False := by
  classical
  let f2 := fourCliqueLongHeptagon q t 2
  let f3 := fourCliqueLongHeptagon q t 3
  have hf2 : IsHeptagon G f2 := fourCliqueLongHeptagon_isHeptagon q t hq ht hqt
    hclique hleft h01 h12 h23 hright 2 (by decide) (by decide)
  have hf3 : IsHeptagon G f3 := fourCliqueLongHeptagon_isHeptagon q t hq ht hqt
    hclique hleft h01 h12 h23 hright 3 (by decide) (by decide)
  have h2w : ∀ i, f2 i ≠ w := by
    intro i
    fin_cases i <;> simp [f2, fourCliqueLongHeptagon, hqw, htw]
  have h3w : ∀ i, f3 i ≠ w := by
    intro i
    fin_cases i <;> simp [f3, fourCliqueLongHeptagon, hqw, htw]
  let g2 : Fin 7 → Fin 7 := fun i => c ⟨f2 i, h2w i⟩
  let g3 : Fin 7 → Fin 7 := fun i => c ⟨f3 i, h3w i⟩
  have hi2 : Function.Injective g2 := rainbow_heptagon_colors_injective hr w c f2 hf2 h2w
  have hi3 : Function.Injective g3 := rainbow_heptagon_colors_injective hr w c f3 hf3 h3w
  let qc : Fin 4 → Fin 7 := fun i => c ⟨q i, hqw i⟩
  let tc : Fin 4 → Fin 7 := fun i => c ⟨t i, htw i⟩
  have hqi : Function.Injective qc := by
    intro i j hij
    by_contra hne
    have ha : (G.induce {x | x ≠ w}).Adj ⟨q i, hqw i⟩ ⟨q j, hqw j⟩ :=
      hclique i j hne
    exact (c.valid ha) hij
  let idx : Fin 4 → Fin 7 := ![1, 2, 3, 4]
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
    · have he : g2 5 = g2 (idx j) := by
        change qc 1 = (g2 ∘ idx) j
        rw [he2]
        exact hij
      have hh := hi2 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g2 6 = g2 (idx j) := by
        change qc 2 = (g2 ∘ idx) j
        rw [he2]
        exact hij
      have hh := hi2 he
      fin_cases j <;> norm_num [idx] at hh
    · have he : g3 6 = g3 (idx j) := by
        change qc 3 = (g3 ∘ idx) j
        rw [he3]
        exact hij
      have hh := hi3 he
      fin_cases j <;> norm_num [idx] at hh
  have height : Function.Injective (Fin.append qc tc) :=
    Fin.append_injective_iff.mpr ⟨hqi, hti, hcross⟩
  have hcard := Fintype.card_le_of_injective (Fin.append qc tc) height
  norm_num at hcard

theorem critical_no_four_clique_external_four_path [Fintype V]
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 4 → V) (t : Fin 4 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hleft : G.Adj (q 0) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (h23 : G.Adj (t 2) (t 3))
    (hright : G.Adj (t 3) (q 1)) : False := by
  classical
  let S := (Finset.univ.image q) ∪ (Finset.univ.image t)
  have hqcard : (Finset.univ.image q).card ≤ 4 := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := q)
  have htcard : (Finset.univ.image t).card ≤ 4 := by
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
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  exact four_clique_long_path_coloring_incompatible hr w c q t hq ht hqt hqw htw
    hclique hleft h01 h12 h23 hright

end TaskH.Seven

#print axioms TaskH.Seven.fourCliqueLongHeptagon
#print axioms TaskH.Seven.fourCliqueLongHeptagon_injective
#print axioms TaskH.Seven.fourCliqueLongHeptagon_isHeptagon
#print axioms TaskH.Seven.four_clique_long_path_coloring_incompatible
#print axioms TaskH.Seven.critical_no_four_clique_external_four_path
