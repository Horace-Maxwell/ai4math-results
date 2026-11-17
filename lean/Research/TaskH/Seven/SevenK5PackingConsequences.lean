import Research.TaskH.Seven.SevenK5PackingRepresentatives
import Research.TaskH.Seven.SevenK6Free

/-! The three actual attachment-label cases remaining for a putative K5.
No K5 exclusion is asserted by this intermediate source. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem fiveClique_packing_cases
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn51 : Fintype.card V ≤ 51)
    (hdegree : ∀ x : V, 10 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    ((fiveCliqueActiveLabels G q).card = 0 ∧
      6 ≤ (fiveCliqueMulti G q).card ∧ (fiveCliqueMulti G q).card ≤ 9) ∨
    ((fiveCliqueActiveLabels G q).card = 1 ∧
      6 ≤ (fiveCliqueMulti G q).card ∧ (fiveCliqueMulti G q).card ≤ 7) ∨
    ((fiveCliqueActiveLabels G q).card = 5 ∧ (fiveCliqueMulti G q).card = 0) := by
  let r := (fiveCliqueMulti G q).card
  let p := (fiveCliqueActiveLabels G q).card
  have hp : p ≤ 5 := fiveCliqueActiveLabels_card_le_five q
  have hpack := fiveClique_full_open_packing hcrit hr hn9 q hq hclique 10 hdegree
  change (10 - 5) * r + (10 - 1) * p ≤ Fintype.card V - 5 at hpack
  norm_num at hpack
  have hmissing : p < 5 → 6 ≤ r := by
    intro hlt
    have hh := fiveClique_missing_singleton_many_multi q hq hclique 10 hdegree hlt
    change 10 - 4 ≤ r at hh
    norm_num at hh
    exact hh
  by_cases hp5 : p = 5
  · exact Or.inr (Or.inr ⟨hp5, by omega⟩)
  · have hr := hmissing (by omega)
    by_cases hp0 : p = 0
    · exact Or.inl ⟨hp0, hr, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, hr, by omega⟩)

theorem equality_fiveClique_packing_cases
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    ((fiveCliqueActiveLabels G q).card = 0 ∧
      6 ≤ (fiveCliqueMulti G q).card ∧ (fiveCliqueMulti G q).card ≤ 9) ∨
    ((fiveCliqueActiveLabels G q).card = 1 ∧
      6 ≤ (fiveCliqueMulti G q).card ∧ (fiveCliqueMulti G q).card ≤ 7) ∨
    ((fiveCliqueActiveLabels G q).card = 5 ∧ (fiveCliqueMulti G q).card = 0) := by
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn9 := noncomplete_card_ge_nine hcrit hs hr hnot
  exact fiveClique_packing_cases hcrit hr hn9
    (critical_card_le_fifty_one hcrit hs hr hn9 hc)
    (fun x => equality_noncomplete_degree_ge_ten hcrit hc hnot x) q hq hclique

end TaskH.Seven
#print axioms TaskH.Seven.fiveClique_packing_cases
#print axioms TaskH.Seven.equality_fiveClique_packing_cases
