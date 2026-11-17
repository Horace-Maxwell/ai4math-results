import Research.TaskH.Seven.SevenK5PackingConsequences
import Research.TaskH.Seven.SevenK5PackingHeavy

/-! Actual missing singleton labels demand at least six incidences per root.
The original packing cases p=0 and p=1 contradict the real ≤3r+2 upper bound.
The last p=5/r=0 closed-neighborhood averaging branch is NOT asserted here. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem fiveClique_inactive_root_multi_neighbors
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (i : Fin 5) (hi : i ∉ fiveCliqueActiveLabels G q) :
    6 ≤ ((fiveCliqueMulti G q).filter (fun x => i ∈ fiveCliqueLabels G q x)).card := by
  classical
  have hnone : ¬ (fiveCliqueSingleGroup G q i).Nonempty := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsub : packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i) ⊆
      (fiveCliqueMulti G q).filter (fun x => i ∈ fiveCliqueLabels G q x) := by
    intro x hx
    have hh := Finset.mem_filter.mp hx
    have hiL : i ∈ fiveCliqueLabels G q x := by
      simpa only [fiveCliqueLabels, Finset.mem_filter, Finset.mem_univ, true_and]
        using hh.2.symm
    have hl : 2 ≤ (fiveCliqueLabels G q x).card := by
      by_contra hsmall
      have hle : (fiveCliqueLabels G q x).card ≤ 1 := by omega
      have he : fiveCliqueLabels G q x = {i} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hiL, fun j hj => Finset.card_le_one.mp hle j hj i hiL⟩
      exact hnone ⟨x, Finset.mem_filter.mpr ⟨hh.1, he⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hh.1, hl⟩, hiL⟩
  have hout := packingNeighborsIn_compl_lower (fiveCliqueSet q) (q i) 10 4
    (hdegree _) (fiveClique_root_internal_neighbors_card q hq hclique i).le
  have hout' : 6 ≤ (packingNeighborsIn G (fiveCliqueSet q)ᶜ (q i)).card := by
    simpa using hout
  exact hout'.trans (Finset.card_le_card hsub)

theorem fiveClique_inactive_incidence_lower
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hdegree : ∀ x : V, 10 ≤ G.degree x) :
    6 * (fiveCliqueActiveLabels G q)ᶜ.card ≤
      ∑ x ∈ fiveCliqueMulti G q, (fiveCliqueLabels G q x).card := by
  classical
  let U := (fiveCliqueActiveLabels G q)ᶜ
  let M := fiveCliqueMulti G q
  have hrow : ∀ i ∈ U, 6 ≤ (M.filter (fun x => i ∈ fiveCliqueLabels G q x)).card := by
    intro i hi
    exact fiveClique_inactive_root_multi_neighbors q hq hclique hdegree i
      (Finset.mem_compl.mp hi)
  have hlow : 6 * U.card ≤ ∑ i ∈ U, (M.filter (fun x => i ∈ fiveCliqueLabels G q x)).card := by
    calc
      _ = ∑ _i ∈ U, 6 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hdouble : (∑ i ∈ U, (M.filter (fun x => i ∈ fiveCliqueLabels G q x)).card) =
      ∑ x ∈ M, (U.filter (fun i => i ∈ fiveCliqueLabels G q x)).card := by
    convert FiniteBudget.relation_double_count U M (fun i x => i ∈ fiveCliqueLabels G q x)
      using 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro x _
      congr 1
      ext z
      simp only [Finset.mem_filter]
  have hupper : (∑ x ∈ M, (U.filter (fun i => i ∈ fiveCliqueLabels G q x)).card) ≤
      ∑ x ∈ M, (fiveCliqueLabels G q x).card := by
    apply Finset.sum_le_sum
    intro x _hx
    exact Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
  exact hlow.trans (hdouble.le.trans hupper)

theorem fiveClique_no_at_most_one_active_label
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn51 : Fintype.card V ≤ 51)
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hp : (fiveCliqueActiveLabels G q).card ≤ 1) : False := by
  classical
  have hcases := fiveClique_packing_cases hcrit hr hn9 hn51 hdegree q hq hclique
  have hlower := fiveClique_inactive_incidence_lower q hq hclique hdegree
  have hc := Finset.card_add_card_compl (fiveCliqueActiveLabels G q)
  have hc' : (fiveCliqueActiveLabels G q).card +
      (fiveCliqueActiveLabels G q)ᶜ.card = 5 := by
    change (fiveCliqueActiveLabels G q).card + (fiveCliqueActiveLabels G q)ᶜ.card = 5 at hc
    exact hc
  rcases hcases with ⟨hp0, hr6, hr9⟩ | ⟨hp1, hr6, hr7⟩ | ⟨hp5, _hr0⟩
  · have hupper := fiveClique_multi_label_incidence_le hcrit hr hn9 q hq hclique (by omega)
    omega
  · have hupper := fiveClique_multi_label_incidence_le hcrit hr hn9 q hq hclique (by omega)
    omega
  · omega

theorem equality_fiveClique_all_active_no_multi
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    (fiveCliqueActiveLabels G q).card = 5 ∧ (fiveCliqueMulti G q).card = 0 := by
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn9 := noncomplete_card_ge_nine hcrit hs hr hnot
  have hn51 := critical_card_le_fifty_one hcrit hs hr hn9 hc
  have hd : ∀ x : V, 10 ≤ G.degree x := fun x =>
    equality_noncomplete_degree_ge_ten hcrit hc hnot x
  rcases fiveClique_packing_cases hcrit hr hn9 hn51 hd q hq hclique
    with ⟨hp0, _hr6, _hr9⟩ | ⟨hp1, _hr6, _hr7⟩ | hlast
  · exact (fiveClique_no_at_most_one_active_label hcrit hr hn9 hn51 hd q hq hclique
      (by omega)).elim
  · exact (fiveClique_no_at_most_one_active_label hcrit hr hn9 hn51 hd q hq hclique
      (by omega)).elim
  · exact hlast

end TaskH.Seven
#print axioms TaskH.Seven.fiveClique_inactive_root_multi_neighbors
#print axioms TaskH.Seven.fiveClique_inactive_incidence_lower
#print axioms TaskH.Seven.fiveClique_no_at_most_one_active_label
#print axioms TaskH.Seven.equality_fiveClique_all_active_no_multi
