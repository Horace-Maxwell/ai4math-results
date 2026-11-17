import Research.TaskH.Seven.SevenFirstStep
import Research.TaskH.Seven.SevenK5Free
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Original degree eleven leaves exactly three singleton colors and four
actual two-point neighbor-color fibers; no fiber pattern is assumed. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degree_eleven_fiber_pattern
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 11) :
    (singletonNeighborColors v c).card = 3 ∧
      ∀ i : Fin 7, (neighborColorFiber v c i).card =
        if i ∈ singletonNeighborColors v c then 1 else 2 := by
  classical
  let S := singletonNeighborColors v c
  have hlow := singletonNeighborColors_card_ge hcrit v c
  have hhigh := singleton_colors_card_lt_four_of_cliqueFree_five hcrit hs hr hfree v c
  have hS : S.card = 3 := by
    rw [hv] at hlow
    change 14 - 11 ≤ S.card at hlow
    change S.card < 4 at hhigh
    omega
  have hpos : ∀ i : Fin 7, 0 < (neighborColorFiber v c i).card := by
    intro i
    obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v c i
    exact Finset.card_pos.mpr ⟨z, (mem_neighborColorFiber v c i z).mpr hz⟩
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin 7)),
      (if i ∈ S then 1 else 2 : ℕ) ≤ (neighborColorFiber v c i).card := by
    intro i _hi
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact ((mem_singletonNeighborColors v c i).mp hi).symm.le
    · rw [ite_eq_right hi]
      have hn : (neighborColorFiber v c i).card ≠ 1 := by
        intro he
        exact hi ((mem_singletonNeighborColors v c i).mpr he)
      have hp := hpos i
      omega
  have hsingle : (∑ i : Fin 7, if i ∈ S then 1 else 0 : ℕ) = S.card := by
    have he : (Finset.univ.filter (fun i : Fin 7 => i ∈ S)) = S := by ext i; simp
    calc
      _ = (Finset.univ.filter (fun i : Fin 7 => i ∈ S)).card := Finset.sum_boole _ _
      _ = _ := congrArg Finset.card he
  have htwo : ∀ i : Fin 7,
      (if i ∈ S then 1 else 2 : ℕ) + (if i ∈ S then 1 else 0 : ℕ) = 2 := by
    intro i
    split_ifs <;> rfl
  have hw : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) = 11 := by
    have hh : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) + S.card = 14 := by
      rw [← hsingle, ← Finset.sum_add_distrib]
      norm_num [htwo]
    omega
  have hsum := sum_neighborColorFiber_card v c
  rw [G.card_neighborSet_eq_degree, hv] at hsum
  have heq : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) =
      ∑ i : Fin 7, (neighborColorFiber v c i).card := hw.trans hsum.symm
  have hpoint := (Finset.sum_eq_sum_iff_of_le hstep).mp heq
  refine ⟨hS, ?_⟩
  intro i
  exact (hpoint i (Finset.mem_univ i)).symm

theorem degree_eleven_two_pair_colors
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 11) :
    ∃ eta gamma : Fin 7, eta ≠ gamma ∧
      eta ∉ singletonNeighborColors v c ∧ gamma ∉ singletonNeighborColors v c ∧
      (neighborColorFiber v c eta).card = 2 ∧ (neighborColorFiber v c gamma).card = 2 := by
  classical
  obtain ⟨hS, hpoint⟩ := degree_eleven_fiber_pattern hcrit hs hr hfree v c hv
  have hcomp : (singletonNeighborColors v c)ᶜ.card = 4 := by
    have hh := Finset.card_add_card_compl (singletonNeighborColors v c)
    rw [hS] at hh
    norm_num at hh
    omega
  obtain ⟨eta, he, gamma, hg, heg⟩ := Finset.one_lt_card.mp (by omega :
    1 < (singletonNeighborColors v c)ᶜ.card)
  have he' := Finset.mem_compl.mp he
  have hg' := Finset.mem_compl.mp hg
  exact ⟨eta, gamma, heg, he', hg', by simpa only [ite_eq_right he'] using hpoint eta,
    by simpa only [ite_eq_right hg'] using hpoint gamma⟩

end TaskH.Seven
#print axioms TaskH.Seven.degree_eleven_fiber_pattern
#print axioms TaskH.Seven.degree_eleven_two_pair_colors
