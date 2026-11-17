import Research.TaskH.Six.SixBipartiteCore
import Research.TaskH.Six.BipartiteSixWords
import Research.TaskH.Six.SixMinimumDegreeNine

/-!
Exclusion of degree nine under the original critical equality hypotheses.
A degree-nine vertex lies on at least 180 counted cycles, reducing the actual
vertex bound to 35. Three actual singleton neighbors supply a four-clique;
its proved packing rigidity supplies an actual K_(4,6), whose 480 distinct
counted six-cycle edge sets contradict the original total 420.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degree_nine_cycleDegree_ge_one_eighty (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (v : V) (hv : G.degree v = 9) :
    180 ≤ cycleDegree G v := by
  have hh := critical_singleton_cycle_bound hcrit hs v
  rw [← cycleDegree_eq_ncard, hv] at hh
  norm_num at hh
  exact hh

theorem critical_cycleDegree_root_incidence (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420)
    (v : V) (a : ℕ) (ha : a ≤ cycleDegree G v) :
    a + 68 * (Fintype.card V - 1) ≤ 2520 := by
  have hlo : 68 * ((Finset.univ : Finset V).erase v).card ≤
      ∑ x ∈ (Finset.univ : Finset V).erase v, cycleDegree G x := by
    calc
      _ = ∑ _x ∈ (Finset.univ : Finset V).erase v, 68 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x _ =>
        (critical_cycleDegree_and_degree_bounds hcrit hs hr hn8 hc x).1)
  have hcard : ((Finset.univ : Finset V).erase v).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  rw [hcard] at hlo
  have hsum := Finset.sum_erase_add (Finset.univ : Finset V)
    (cycleDegree G) (Finset.mem_univ v)
  rw [sum_cycleDegree_eq_2520 hs hc] at hsum
  omega

theorem critical_degree_nine_card_le_thirty_five (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420)
    (v : V) (hv : G.degree v = 9) : Fintype.card V ≤ 35 := by
  have ha := degree_nine_cycleDegree_ge_one_eighty hcrit hs v hv
  have hb := critical_cycleDegree_root_incidence hcrit hs hr hn8 hc v 180 ha
  exact degree_nine_card_le_thirty_five (Fintype.card V) (by omega) hb

theorem critical_degree_nine_has_four_clique (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 9) :
    ∃ q : Fin 4 → V, Function.Injective q ∧
      ∀ i j : Fin 4, i ≠ j → G.Adj (q i) (q j) := by
  have hlo := singletonNeighborColors_card_ge hcrit v c
  rw [hv] at hlo
  have hthree : 3 ≤ (singletonNeighborColors v c).card := by omega
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card ↥(singletonNeighborColors v c) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hthree
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let N : Fin 3 → V := fun i => (singletonNeighbor v c (e i)).val
  have hNi : Function.Injective N := (singletonNeighbor_val_injective v c).comp e.injective
  have hroot : ∀ i : Fin 3, G.Adj v (N i) :=
    fun i => (singletonNeighbor v c (e i)).property
  have hroot' : ∀ i : Fin 3, G.Adj (N i) v := fun i => (hroot i).symm
  have hNv : ∀ i : Fin 3, v ≠ N i := fun i => (hroot i).ne
  have hNv' : ∀ i : Fin 3, N i ≠ v := fun i => (hNv i).symm
  have hNN : ∀ i j : Fin 3, i ≠ j → G.Adj (N i) (N j) := by
    intro i j hij
    exact singleton_neighbors_adj hcrit hs hr v c hthree (e i) (e j) (e.injective.ne hij)
  let q : Fin 4 → V := ![v, N 0, N 1, N 2]
  have hqi : Function.Injective q := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [q, hNi.eq_iff]
  have hqa : ∀ i j : Fin 4, i ≠ j → G.Adj (q i) (q j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  exact ⟨q, hqi, hqa⟩

theorem critical_degree_ne_nine (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn8 : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420)
    (hdegree : ∀ x : V, 9 ≤ G.degree x) (v : V) : G.degree v ≠ 9 := by
  intro hv
  have hn35 := critical_degree_nine_card_le_thirty_five hcrit hs hr hn8 hc v hv
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit v
  obtain ⟨q, hq, hclique⟩ := critical_degree_nine_has_four_clique hcrit hs hr v c hv
  obtain ⟨t, ht, hqt, hcross⟩ := degree_nine_four_clique_has_actual_bipartite_core
    hcrit hr hn8 hn35 hdegree q hq hclique
  have h480 := actual_bipartite_four_six_modCycleCount_ge q t hq ht hqt hcross
  rw [hc] at h480
  exact complete_bipartite_six_cycle_budget_incompatible h480

theorem equality_degree_ne_nine (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) (v : V) :
    G.degree v ≠ 9 := by
  have hs : ShortSixCycles G := equality_shortSixCycles hcrit hc
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hn8 := (critical_noncomplete_bounds hcrit hs hr hc hnot).1
  exact critical_degree_ne_nine hcrit hs hr hn8 hc
    (equality_degree_ge_nine hcrit hc hnot) v

theorem equality_degree_ge_ten (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    ∀ v : V, 10 ≤ G.degree v := by
  intro v
  have hlow := equality_degree_ge_nine hcrit hc hnot v
  have hne := equality_degree_ne_nine hcrit hc hnot v
  omega

theorem equality_minDegree_ge_ten (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) : 10 ≤ G.minDegree := by
  have hn := critical_six_card_ge_seven hcrit
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact G.le_minDegree_of_forall_le_degree 10 (equality_degree_ge_ten hcrit hc hnot)

end TaskH.Six

#print axioms TaskH.Six.degree_nine_cycleDegree_ge_one_eighty
#print axioms TaskH.Six.critical_cycleDegree_root_incidence
#print axioms TaskH.Six.critical_degree_nine_card_le_thirty_five
#print axioms TaskH.Six.critical_degree_nine_has_four_clique
#print axioms TaskH.Six.critical_degree_ne_nine
#print axioms TaskH.Six.equality_degree_ne_nine
#print axioms TaskH.Six.equality_degree_ge_ten
#print axioms TaskH.Six.equality_minDegree_ge_ten
