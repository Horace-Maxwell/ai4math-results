import Research.TaskH.Seven.SevenTwoColorFrame
import Research.TaskH.Seven.SevenTwoColorSwapFibers

/-! Actual neighbor-fiber transport through a Kempe exchange. Only the fixed
old Frame is required pure split. Original all-colorings first-step coverage
is used on the genuinely recolored graph; no pure-split property of the new
coloring is assumed. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem twoColorSwap_fixed_color_iff {W : Type*} {K : SimpleGraph W}
    (c : K.Coloring (Fin 7)) (alpha beta gamma : Fin 7) (a z : W)
    (hga : gamma ≠ alpha) (hgb : gamma ≠ beta) :
    twoColorSwap c alpha beta a z = gamma ↔ c z = gamma := by
  rw [twoColorSwap_apply]
  split_ifs
  · rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hga hgb]
  · rfl

theorem DegreeTwelveFrame.singleton_fiber_as_deleted {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) (z : {x : V // x ≠ v})
    (hz : G.Adj v z.val) :
    c z = (F.singletonIndex j).val ↔ z = F.centerD j := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  constructor
  · intro hcol
    let zz : G.neighborSet v := ⟨z.val, hz⟩
    have he := singletonNeighbor_eq_of_color v c (F.singletonIndex j) zz hcol
    apply Subtype.ext
    change z.val = (singletonNeighbor v c (F.singletonIndex j)).val
    exact congrArg (fun w : G.neighborSet v => w.val) he
  · intro he
    subst z
    exact F.center_color j

theorem DegreeTwelveFrame.pair_fiber_as_deleted {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (z : {x : V // x ≠ v})
    (hz : G.Adj v z.val) :
    c z = (F.pairIndex i).val ↔ z = F.splitAD i ∨ z = F.splitBD i := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  constructor
  · intro hcol
    let zz : G.neighborSet v := ⟨z.val, hz⟩
    let zf : ↥(neighborColorFiber v c (F.pairIndex i).val) :=
      ⟨zz, (mem_neighborColorFiber v c _ zz).mpr hcol⟩
    obtain ⟨e, he⟩ := (F.pairVertices i).surjective zf
    have hleaf : (F.leaf i e).val = z.val := congrArg (fun w => w.val.val) he
    have hchoices : F.leaf i e = F.splitA i ∨ F.leaf i e = F.splitB i := by
      unfold DegreeTwelveFrame.splitA DegreeTwelveFrame.splitB
      split_ifs <;> fin_cases e <;> simp
    rcases hchoices with hh | hh
    · left
      exact Subtype.ext (hleaf.symm.trans (congrArg Subtype.val hh))
    · right
      exact Subtype.ext (hleaf.symm.trans (congrArg Subtype.val hh))
  · rintro (he | he)
    · subst z
      exact F.splitA_color i
    · subst z
      exact F.splitB_color i

noncomputable def DegreeTwelveFrame.swapOnPair {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) :
    (G.induce {x | x ≠ v}).Coloring (Fin 7) :=
  twoColorSwap c (F.singletonIndex 0).val (F.pairIndex i).val (F.centerD 0)

theorem DegreeTwelveFrame.swapOnPair_singleton_fiber {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (hout : F.splitBD i ∉ twoColorComponent c (F.singletonIndex 0).val
      (F.pairIndex i).val (F.centerD 0)) :
    neighborColorFiber v (F.swapOnPair i) (F.singletonIndex 0).val = {F.splitA i} := by
  have hi := F.splitAB_adjacencies i (hF i)
  have hswap := twoColorSwap_singleton_pair_fibers c (F.singletonIndex 0).val
    (F.pairIndex i).val (F.centerD 0) (F.splitAD i) (F.splitBD i)
    {z : {x : V // x ≠ v} | G.Adj v z.val}
    (F.center_color 0) (F.splitA_color i) hi.1
    (fun z hz => F.singleton_fiber_as_deleted 0 z hz)
    (fun z hz => F.pair_fiber_as_deleted i z hz) hout
  ext z
  rw [mem_neighborColorFiber, Finset.mem_singleton]
  change twoColorSwap c (F.singletonIndex 0).val (F.pairIndex i).val
    (F.centerD 0) (twoColorNeighborDeleted v z) = (F.singletonIndex 0).val ↔ z = F.splitA i
  rw [hswap.1 _ z.property]
  constructor
  · intro he
    apply Subtype.ext
    exact congrArg (fun w : {x : V // x ≠ v} => w.val) he
  · intro he
    apply Subtype.ext
    exact congrArg (fun w : G.neighborSet v => w.val) he

theorem DegreeTwelveFrame.swapOnPair_other_fiber {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j : Fin 5) (hji : j ≠ i) :
    neighborColorFiber v (F.swapOnPair i) (F.pairIndex j).val =
      neighborColorFiber v c (F.pairIndex j).val := by
  ext z
  rw [mem_neighborColorFiber, mem_neighborColorFiber]
  exact twoColorSwap_fixed_color_iff c (F.singletonIndex 0).val (F.pairIndex i).val
    (F.pairIndex j).val (F.centerD 0) (twoColorNeighborDeleted v z)
    (F.pairColor_ne_singleton j 0) (F.pairColor_injective.ne hji)

theorem DegreeTwelveFrame.disconnected_pair_universal_A
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (hout : F.splitBD i ∉ twoColorComponent c (F.singletonIndex 0).val
      (F.pairIndex i).val (F.centerD 0)) :
    ∀ j : Fin 5, j ≠ i → G.Adj (F.splitA i).val (F.splitA j).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let d := F.swapOnPair i
  have halpha : (F.singletonIndex 0).val ∈ singletonNeighborColors v d := by
    apply (mem_singletonNeighborColors v d _).mpr
    rw [F.swapOnPair_singleton_fiber hF i hout, Finset.card_singleton]
  let jj : ↥(singletonNeighborColors v d) := ⟨(F.singletonIndex 0).val, halpha⟩
  have hcenter : singletonNeighbor v d jj = F.splitA i := by
    have hm := singletonNeighbor_fiber v d jj
    rw [F.swapOnPair_singleton_fiber hF i hout] at hm
    exact (Finset.singleton_injective hm).symm
  intro j hji
  have htwo : (neighborColorFiber v c (F.pairIndex j).val).card = 2 := by
    have hh := Fintype.card_congr (F.pairVertices j)
    simpa only [Fintype.card_fin, Fintype.card_coe] using hh.symm
  have hnonsingle : (F.pairIndex j).val ∉ singletonNeighborColors v d := by
    intro he
    have h1 := (mem_singletonNeighborColors v d _).mp he
    rw [F.swapOnPair_other_fiber i j hji, htwo] at h1
    omega
  obtain ⟨z, hzc, hzad⟩ := equality_degree_twelve_singleton_meets_pair
    hcrit hc hnot v d hv jj (F.pairIndex j).val hnonsingle
  rw [hcenter] at hzad
  have hzold : neighborColor v c z = (F.pairIndex j).val := by
    have hfix := twoColorSwap_fixed_color_iff c (F.singletonIndex 0).val (F.pairIndex i).val
      (F.pairIndex j).val (F.centerD 0) (twoColorNeighborDeleted v z)
      (F.pairColor_ne_singleton j 0) (F.pairColor_injective.ne hji)
    exact hfix.mp hzc
  rcases (F.pair_fiber_as_deleted j (twoColorNeighborDeleted v z) z.property).mp hzold with he | he
  · have hz : z.val = (F.splitA j).val :=
      congrArg (fun w : {x : V // x ≠ v} => w.val) he
    rw [hz] at hzad
    exact hzad.symm
  · have hz : z.val = (F.splitB j).val :=
      congrArg (fun w : {x : V // x ≠ v} => w.val) he
    rw [hz] at hzad
    exact False.elim (F.pureSplit_cross_not_adj (equality_rainbowSevenCycles hcrit hc)
      hF i j hzad.symm)

end TaskH.Seven
#print axioms TaskH.Seven.twoColorSwap_fixed_color_iff
#print axioms TaskH.Seven.DegreeTwelveFrame.singleton_fiber_as_deleted
#print axioms TaskH.Seven.DegreeTwelveFrame.pair_fiber_as_deleted
#print axioms TaskH.Seven.DegreeTwelveFrame.swapOnPair
#print axioms TaskH.Seven.DegreeTwelveFrame.swapOnPair_singleton_fiber
#print axioms TaskH.Seven.DegreeTwelveFrame.swapOnPair_other_fiber
#print axioms TaskH.Seven.DegreeTwelveFrame.disconnected_pair_universal_A
