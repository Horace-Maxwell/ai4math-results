import Research.TaskH.Seven.SevenK5PackingLabels
import Research.TaskH.Seven.SevenCliqueRainbow
import Mathlib.Logic.Equiv.Fintype

/-! A compatible pair of actual Q5 attachment labels closes a genuine C7
through all five clique points. The same deleted coloring supplies all three
color restrictions; no two-color premise is substituted for the graph. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem five_labels_four_distinct_roots (I J : Finset (Fin 5))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hU : 4 ≤ (I ∪ J).card) :
    ∃ r : Fin 4 → Fin 5, Function.Injective r ∧
      r 0 ∈ I ∧ r 1 ∈ I ∧ r 2 ∈ J ∧ r 3 ∈ J := by
  have ht : ∀ I J : Finset (Fin 5), 2 ≤ I.card → 2 ≤ J.card →
      4 ≤ (I ∪ J).card →
      ∃ r : Fin 4 → Fin 5, Function.Injective r ∧
        r 0 ∈ I ∧ r 1 ∈ I ∧ r 2 ∈ J ∧ r 3 ∈ J := by
    decide +kernel
  exact ht I J hI hJ hU

def fiveCliqueCompatibleHeptagon (q : Fin 5 → V) (x y : V) : Fin 7 → V :=
  ![x, q 0, q 4, q 2, y, q 3, q 1]

theorem fiveCliqueCompatibleHeptagon_isHeptagon
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (x y : V) (hxy : x ≠ y)
    (hx : ∀ i, x ≠ q i) (hy : ∀ i, y ≠ q i)
    (hx0 : G.Adj x (q 0)) (hx1 : G.Adj x (q 1))
    (hy2 : G.Adj y (q 2)) (hy3 : G.Adj y (q 3)) :
    IsHeptagon G (fiveCliqueCompatibleHeptagon q x y) := by
  have hqx : ∀ i, q i ≠ x := fun i he => hx i he.symm
  have hqy : ∀ i, q i ≠ y := fun i he => hy i he.symm
  refine ⟨?_, hx0, hclique 0 4 (by decide), hclique 4 2 (by decide),
    hy2.symm, hy3, hclique 3 1 (by decide), hx1.symm⟩
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [fiveCliqueCompatibleHeptagon, hq.eq_iff]

theorem five_clique_compatible_color_constraints
    (hr : RainbowSevenCycles G) (w : V)
    (c : (G.induce {z | z ≠ w}).Coloring (Fin 7))
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hqw : ∀ i, q i ≠ w)
    (x y : V) (hxw : x ≠ w) (hyw : y ≠ w) (hxy : x ≠ y)
    (hx : ∀ i, x ≠ q i) (hy : ∀ i, y ≠ q i)
    (hxL : 2 ≤ (fiveCliqueLabels G q x).card)
    (hyL : 2 ≤ (fiveCliqueLabels G q y).card)
    (hunion : 4 ≤ (fiveCliqueLabels G q x ∪ fiveCliqueLabels G q y).card) :
    c ⟨x, hxw⟩ ≠ c ⟨y, hyw⟩ ∧
      (∀ i, c ⟨x, hxw⟩ ≠ c ⟨q i, hqw i⟩) ∧
      (∀ i, c ⟨y, hyw⟩ ≠ c ⟨q i, hqw i⟩) := by
  classical
  obtain ⟨r, hrinj, hr0, hr1, hr2, hr3⟩ :=
    five_labels_four_distinct_roots _ _ hxL hyL hunion
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 4 => i.castSucc) r (Fin.castSucc_injective 4) hrinj
  have hπ0 : π 0 = r 0 := hπ 0
  have hπ1 : π 1 = r 1 := hπ 1
  have hπ2 : π 2 = r 2 := hπ 2
  have hπ3 : π 3 = r 3 := hπ 3
  let p := q ∘ π
  have hp : Function.Injective p := hq.comp π.injective
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique _ _ (π.injective.ne hij)
  have hx0 : G.Adj x (p 0) := by
    change G.Adj x (q (π 0))
    rw [hπ0]
    exact (Finset.mem_filter.mp hr0).2
  have hx1 : G.Adj x (p 1) := by
    change G.Adj x (q (π 1))
    rw [hπ1]
    exact (Finset.mem_filter.mp hr1).2
  have hy2 : G.Adj y (p 2) := by
    change G.Adj y (q (π 2))
    rw [hπ2]
    exact (Finset.mem_filter.mp hr2).2
  have hy3 : G.Adj y (p 3) := by
    change G.Adj y (q (π 3))
    rw [hπ3]
    exact (Finset.mem_filter.mp hr3).2
  let f := fiveCliqueCompatibleHeptagon p x y
  have hf : IsHeptagon G f := fiveCliqueCompatibleHeptagon_isHeptagon p hp hpclique
    x y hxy (fun i => hx (π i)) (fun i => hy (π i)) hx0 hx1 hy2 hy3
  have hfw : ∀ i, f i ≠ w := by
    intro i
    fin_cases i <;> simp [f, fiveCliqueCompatibleHeptagon, p, hxw, hyw, hqw]
  have hci := rainbow_heptagon_colors_injective hr w c f hf hfw
  let idx : Fin 5 → Fin 7 := ![1, 6, 3, 5, 2]
  have he : ∀ i, f (idx i) = p i := by intro i; fin_cases i <;> rfl
  have hxne : ∀ i, c ⟨x, hxw⟩ ≠ c ⟨p i, hqw (π i)⟩ := by
    intro i hc
    have hsub : (⟨f (idx i), hfw (idx i)⟩ : {z : V // z ≠ w}) =
        ⟨p i, hqw (π i)⟩ := Subtype.ext (he i)
    have hh : (0 : Fin 7) = idx i := by
      apply hci
      change c ⟨x, hxw⟩ = c ⟨f (idx i), hfw (idx i)⟩
      rw [hsub]
      exact hc
    fin_cases i <;> norm_num [idx] at hh
  have hyne : ∀ i, c ⟨y, hyw⟩ ≠ c ⟨p i, hqw (π i)⟩ := by
    intro i hc
    have hsub : (⟨f (idx i), hfw (idx i)⟩ : {z : V // z ≠ w}) =
        ⟨p i, hqw (π i)⟩ := Subtype.ext (he i)
    have hh : (4 : Fin 7) = idx i := by
      apply hci
      change c ⟨y, hyw⟩ = c ⟨f (idx i), hfw (idx i)⟩
      rw [hsub]
      exact hc
    fin_cases i <;> norm_num [idx] at hh
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    have hh : (0 : Fin 7) = 4 := hci hc
    exact (by decide : (0 : Fin 7) ≠ 4) hh
  · intro i
    obtain ⟨j, rfl⟩ := π.surjective i
    exact hxne j
  · intro i
    obtain ⟨j, rfl⟩ := π.surjective i
    exact hyne j

end TaskH.Seven
#print axioms TaskH.Seven.five_labels_four_distinct_roots
#print axioms TaskH.Seven.fiveCliqueCompatibleHeptagon
#print axioms TaskH.Seven.fiveCliqueCompatibleHeptagon_isHeptagon
#print axioms TaskH.Seven.five_clique_compatible_color_constraints
