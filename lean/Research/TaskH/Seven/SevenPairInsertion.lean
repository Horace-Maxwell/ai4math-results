import Research.TaskH.Seven.SevenDegreeElevenFibers

/-! A three-center label certificate and its actual seven-cycle transport.
Only the three finite center indices are decided; no graph/order family or
actual-neighbor configuration is enumerated or assumed by the main wrapper. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

noncomputable def centerLabels (G : SimpleGraph V) (q : Fin 3 → V) (x : V) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => G.Adj x (q i))

theorem three_center_insert_indices (A B Z : Finset (Fin 3))
    (hcover : A ∪ B = Finset.univ) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hZ : 2 ≤ Z.card) :
    ∃ a b d : Fin 3, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ a ∈ A ∧ d ∈ B ∧
      ((a ∈ Z ∧ b ∈ Z) ∨ (b ∈ Z ∧ d ∈ Z)) := by
  have ht : ∀ A B Z : Finset (Fin 3), A ∪ B = Finset.univ →
      A ≠ Finset.univ → B ≠ Finset.univ → 2 ≤ Z.card →
      ∃ a b d : Fin 3, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ a ∈ A ∧ d ∈ B ∧
        ((a ∈ Z ∧ b ∈ Z) ∨ (b ∈ Z ∧ d ∈ Z)) := by
    decide +kernel
  exact ht A B Z hcover hA hB hZ

def centerInsertHeptagon (v x y z : V) (q : Fin 3 → V)
    (a b d : Fin 3) (left : Bool) : Fin 7 → V :=
  if left then ![v, x, q a, z, q b, q d, y] else ![v, x, q a, q b, z, q d, y]

theorem centerInsertHeptagon_injective (v x y z : V) (q : Fin 3 → V)
    (hq : Function.Injective q) (hvq : ∀ i, G.Adj v (q i))
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxq : ∀ i, x ≠ q i) (hyq : ∀ i, y ≠ q i) (hzq : ∀ i, z ≠ q i)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (left : Bool) :
    Function.Injective (centerInsertHeptagon v x y z q a b d left) := by
  have hqv : ∀ i, q i ≠ v := fun i => (hvq i).ne.symm
  have hvqi : ∀ i, v ≠ q i := fun i => (hvq i).ne
  have hqx : ∀ i, q i ≠ x := fun i he => hxq i he.symm
  have hqy : ∀ i, q i ≠ y := fun i he => hyq i he.symm
  have hqz : ∀ i, q i ≠ z := fun i he => hzq i he.symm
  have hxv := hvx.ne.symm
  have hyv := hvy.ne.symm
  have hzv := hvz.ne.symm
  have hvxn := hvx.ne
  have hvyn := hvy.ne
  have hvzn := hvz.ne
  have hyx := Ne.symm hxy
  have hzx := Ne.symm hxz
  have hzy := Ne.symm hyz
  cases left <;> intro i j he <;> fin_cases i <;> fin_cases j <;>
    simp_all [centerInsertHeptagon, hq.eq_iff]

theorem center_pair_insertion_false
    (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (q : Fin 3 → V) (hq : Function.Injective q)
    (hqclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (hvq : ∀ i, G.Adj v (q i))
    (x y z : G.neighborSet v) (hxy : x ≠ y)
    (hxz : x.val ≠ z.val) (hyz : y.val ≠ z.val)
    (hxq : ∀ i, x.val ≠ q i) (hyq : ∀ i, y.val ≠ q i) (hzq : ∀ i, z.val ≠ q i)
    (hcolor : neighborColor v c x = neighborColor v c y)
    (hcover : centerLabels G q x.val ∪ centerLabels G q y.val = Finset.univ)
    (hA : centerLabels G q x.val ≠ Finset.univ)
    (hB : centerLabels G q y.val ≠ Finset.univ)
    (hZ : 2 ≤ (centerLabels G q z.val).card) : False := by
  classical
  obtain ⟨a, b, d, hab, had, hbd, ha, hd, hleft | hright⟩ :=
    three_center_insert_indices _ _ _ hcover hA hB hZ
  · let f := centerInsertHeptagon v x.val y.val z.val q a b d true
    have hf : IsHeptagon G f := ⟨centerInsertHeptagon_injective v x.val y.val z.val q hq
      hvq x.property y.property z.property (fun he => hxy (Subtype.ext he)) hxz hyz
      hxq hyq hzq a b d hab had hbd true,
      x.property, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hleft.1).2.symm,
      (Finset.mem_filter.mp hleft.2).2, hqclique b d hbd,
      (Finset.mem_filter.mp hd).2.symm, y.property.symm⟩
    exact rainbow_heptagon_same_color_impossible hr v c f hf x.val y.val
      x.property.ne.symm y.property.ne.symm (fun he => hxy (Subtype.ext he))
      ⟨1, rfl⟩ ⟨6, rfl⟩ hcolor
  · let f := centerInsertHeptagon v x.val y.val z.val q a b d false
    have hf : IsHeptagon G f := ⟨centerInsertHeptagon_injective v x.val y.val z.val q hq
      hvq x.property y.property z.property (fun he => hxy (Subtype.ext he)) hxz hyz
      hxq hyq hzq a b d hab had hbd false,
      x.property, (Finset.mem_filter.mp ha).2, hqclique a b hab,
      (Finset.mem_filter.mp hright.1).2.symm, (Finset.mem_filter.mp hright.2).2,
      (Finset.mem_filter.mp hd).2.symm, y.property.symm⟩
    exact rainbow_heptagon_same_color_impossible hr v c f hf x.val y.val
      x.property.ne.symm y.property.ne.symm (fun he => hxy (Subtype.ext he))
      ⟨1, rfl⟩ ⟨6, rfl⟩ hcolor

theorem cliqueFree_five_center_label_proper
    (hfree : G.CliqueFree 5) (v x : V) (q : Fin 3 → V)
    (hq : Function.Injective q) (hvx : G.Adj v x)
    (hvq : ∀ i, G.Adj v (q i)) (hxq : ∀ i, x ≠ q i)
    (hqq : ∀ i j, i ≠ j → G.Adj (q i) (q j)) :
    centerLabels G q x ≠ Finset.univ := by
  classical
  intro hfull
  have hxadj : ∀ i, G.Adj x (q i) := by
    intro i
    have hm : i ∈ centerLabels G q x := by rw [hfull]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hm).2
  have hqv : ∀ i, q i ≠ v := fun i => (hvq i).ne.symm
  have hvqi : ∀ i, v ≠ q i := fun i => (hvq i).ne
  have hqxi : ∀ i, q i ≠ x := fun i he => hxq i he.symm
  have hxv := hvx.ne.symm
  have hvxn := hvx.ne
  let f : Fin 5 → V := ![v, x, q 0, q 1, q 2]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f, hq.eq_iff]
  have hfa : ∀ i j : Fin 5, i ≠ j → G.Adj (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]
  have hclique : G.IsClique (Finset.univ.image f : Set V) := by
    intro a ha b hb hab
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hb
    exact hfa i j (fun he => hab (congrArg f he))
  have hcard : (Finset.univ.image f).card = 5 := by
    rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin]
  exact hfree (Finset.univ.image f) ⟨hclique, hcard⟩

end TaskH.Seven
#print axioms TaskH.Seven.centerLabels
#print axioms TaskH.Seven.three_center_insert_indices
#print axioms TaskH.Seven.centerInsertHeptagon
#print axioms TaskH.Seven.centerInsertHeptagon_injective
#print axioms TaskH.Seven.center_pair_insertion_false
#print axioms TaskH.Seven.cliqueFree_five_center_label_proper
