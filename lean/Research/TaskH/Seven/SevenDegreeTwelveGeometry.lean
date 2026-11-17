import Research.TaskH.Seven.SevenDegreeTwelveFrame

/-! An actual two-center/five-pair coordinate system derived from each
original degree-twelve deleted coloring. No incidence is encoded as a premise. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure DegreeTwelveFrame (G : SimpleGraph V) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) where
  singletonIndex : Fin 2 ≃ ↥(singletonNeighborColors v c)
  pairIndex : Fin 5 ≃ ↥((singletonNeighborColors v c)ᶜ)
  pairVertices : ∀ i : Fin 5, Fin 2 ≃ ↥(neighborColorFiber v c (pairIndex i).val)

noncomputable def DegreeTwelveFrame.center {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) : G.neighborSet v := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let k : ↥(singletonNeighborColors v c) := by
    cases hdec
    exact F.singletonIndex j
  exact singletonNeighbor v c k

noncomputable def DegreeTwelveFrame.leaf {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (e : Fin 2) : G.neighborSet v :=
  (F.pairVertices i e).val

theorem equality_degreeTwelveFrame
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12) :
    Nonempty (DegreeTwelveFrame G v c) := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  obtain ⟨hS, hfiber⟩ := equality_degree_twelve_fiber_pattern hcrit hc hnot v c hv
  have hP : ((singletonNeighborColors v c)ᶜ).card = 5 := by
    have hh := Finset.card_add_card_compl (singletonNeighborColors v c)
    rw [hS] at hh
    norm_num at hh
    omega
  let es : Fin 2 ≃ ↥(singletonNeighborColors v c) :=
    (Finset.equivFinOfCardEq hS).symm
  let ep : Fin 5 ≃ ↥((singletonNeighborColors v c)ᶜ) :=
    (Finset.equivFinOfCardEq hP).symm
  have htwo : ∀ i : Fin 5, (neighborColorFiber v c (ep i).val).card = 2 := by
    intro i
    rw [hfiber]
    exact ite_eq_right (Finset.mem_compl.mp (ep i).property)
  exact ⟨⟨es, ep, fun i => (Finset.equivFinOfCardEq (htwo i)).symm⟩⟩

theorem DegreeTwelveFrame.center_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) :
    neighborColor v c (F.center j) = (F.singletonIndex j).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  exact singletonNeighbor_color v c (F.singletonIndex j)

theorem DegreeTwelveFrame.leaf_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (e : Fin 2) :
    neighborColor v c (F.leaf i e) = (F.pairIndex i).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let z : ↥(neighborColorFiber v c (F.pairIndex i).val) := by
    cases hdec
    exact F.pairVertices i e
  have hz : z.val = F.leaf i e := by
    cases hdec
    rfl
  rw [← hz]
  exact (mem_neighborColorFiber v c (F.pairIndex i).val z.val).mp z.property

theorem DegreeTwelveFrame.leaf_same_pair_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) :
    Function.Injective (fun e => (F.leaf i e).val) := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let E : Fin 2 ≃ ↥(neighborColorFiber v c (F.pairIndex i).val) := by
    cases hdec
    exact F.pairVertices i
  have hE : ∀ k : Fin 2, (E k).val = F.leaf i k := by
    cases hdec
    intro k
    rfl
  intro e d he
  apply E.injective
  apply Subtype.ext
  apply Subtype.ext
  exact ((congrArg Subtype.val (hE e)).trans he).trans
    (congrArg Subtype.val (hE d)).symm

theorem DegreeTwelveFrame.center_center_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) {i j : Fin 2} (hij : i ≠ j) :
    (F.center i).val ≠ (F.center j).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  intro he
  apply hij
  apply F.singletonIndex.injective
  apply Subtype.ext
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.center_color] using hh

theorem DegreeTwelveFrame.center_leaf_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) (i : Fin 5) (e : Fin 2) :
    (F.center j).val ≠ (F.leaf i e).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  intro he
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  rw [F.center_color, F.leaf_color] at hh
  exact (Finset.mem_compl.mp (F.pairIndex i).property) (hh ▸ (F.singletonIndex j).property)

theorem DegreeTwelveFrame.leaf_leaf_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) {i j : Fin 5} (hij : i ≠ j) (e d : Fin 2) :
    (F.leaf i e).val ≠ (F.leaf j d).val := by
  intro he
  apply hij
  apply F.pairIndex.injective
  apply Subtype.ext
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.leaf_color] using hh

theorem DegreeTwelveFrame.neighbor_cases {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : G.neighborSet v) :
    (∃ j : Fin 2, F.center j = z) ∨ ∃ i : Fin 5, ∃ e : Fin 2, F.leaf i e = z := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  by_cases hz : neighborColor v c z ∈ singletonNeighborColors v c
  · obtain ⟨j, hj⟩ := F.singletonIndex.surjective ⟨neighborColor v c z, hz⟩
    left
    refine ⟨j, ?_⟩
    apply (singletonNeighbor_eq_of_color v c (F.singletonIndex j) z ?_).symm
    exact (congrArg Subtype.val hj).symm
  · let t : ↥((singletonNeighborColors v c)ᶜ) :=
      ⟨neighborColor v c z, Finset.mem_compl.mpr hz⟩
    obtain ⟨i, hi⟩ := F.pairIndex.surjective t
    have hzc : neighborColor v c z = (F.pairIndex i).val :=
      (congrArg Subtype.val hi).symm
    let zz : ↥(neighborColorFiber v c (F.pairIndex i).val) :=
      ⟨z, (mem_neighborColorFiber v c _ z).mpr hzc⟩
    obtain ⟨e, he⟩ := (F.pairVertices i).surjective zz
    right
    exact ⟨i, e, congrArg Subtype.val he⟩

noncomputable def DegreeTwelveFrame.commonColors {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => ∃ e : Fin 2,
    G.Adj (F.center 0).val (F.leaf i e).val ∧
    G.Adj (F.center 1).val (F.leaf i e).val)

def DegreeTwelveFrame.IsPureSplit {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Prop :=
  ∀ i : Fin 5,
    (G.Adj (F.center 0).val (F.leaf i 0).val ∧
      ¬ G.Adj (F.center 1).val (F.leaf i 0).val ∧
      G.Adj (F.center 1).val (F.leaf i 1).val ∧
      ¬ G.Adj (F.center 0).val (F.leaf i 1).val) ∨
    (G.Adj (F.center 0).val (F.leaf i 1).val ∧
      ¬ G.Adj (F.center 1).val (F.leaf i 1).val ∧
      G.Adj (F.center 1).val (F.leaf i 0).val ∧
      ¬ G.Adj (F.center 0).val (F.leaf i 0).val)

theorem DegreeTwelveFrame.center_meets_pair
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (j : Fin 2) (i : Fin 5) :
    ∃ e : Fin 2, G.Adj (F.center j).val (F.leaf i e).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  have hnotS := Finset.mem_compl.mp (F.pairIndex i).property
  obtain ⟨z, hzc, hzadj⟩ := equality_degree_twelve_singleton_meets_pair
    hcrit hc hnot v c hv (F.singletonIndex j) (F.pairIndex i).val hnotS
  let zz : ↥(neighborColorFiber v c (F.pairIndex i).val) :=
    ⟨z, (mem_neighborColorFiber v c _ z).mpr hzc⟩
  obtain ⟨e, he⟩ := (F.pairVertices i).surjective zz
  have hval : (F.leaf i e).val = z.val := congrArg (fun w => w.val.val) he
  exact ⟨e, by rw [hval]; exact hzadj.symm⟩

theorem DegreeTwelveFrame.pureSplit_iff_commonColors_empty
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.IsPureSplit ↔ F.commonColors = ∅ := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  constructor
  · intro hp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨e, ha, hb⟩ := (Finset.mem_filter.mp hi).2
    rcases hp i with h | h <;> fin_cases e <;> simp_all
  · intro he i
    have hno : ¬ ∃ e : Fin 2,
        G.Adj (F.center 0).val (F.leaf i e).val ∧
        G.Adj (F.center 1).val (F.leaf i e).val := by
      intro hx
      have hm : i ∈ F.commonColors := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩
      rw [he] at hm
      exact Finset.notMem_empty i hm
    obtain ⟨e, hae⟩ := F.center_meets_pair hcrit hc hnot hv 0 i
    obtain ⟨d, hbd⟩ := F.center_meets_pair hcrit hc hnot hv 1 i
    have hed : e ≠ d := by
      intro hed
      subst d
      exact hno ⟨e, hae, hbd⟩
    have hbe : ¬ G.Adj (F.center 1).val (F.leaf i e).val :=
      fun hh => hno ⟨e, hae, hh⟩
    have had : ¬ G.Adj (F.center 0).val (F.leaf i d).val :=
      fun hh => hno ⟨d, hh, hbd⟩
    fin_cases e <;> fin_cases d <;> simp_all


noncomputable def DegreeTwelveFrame.swapCenters {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : DegreeTwelveFrame G v c where
  singletonIndex := (Equiv.swap 0 1).trans F.singletonIndex
  pairIndex := F.pairIndex
  pairVertices := F.pairVertices

theorem DegreeTwelveFrame.swapCenters_center_zero {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : F.swapCenters.center 0 = F.center 1 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  change singletonNeighbor v c (F.singletonIndex (Equiv.swap 0 1 0)) = F.center 1
  rw [Equiv.swap_apply_left]
  rfl

theorem DegreeTwelveFrame.swapCenters_center_one {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : F.swapCenters.center 1 = F.center 0 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  change singletonNeighbor v c (F.singletonIndex (Equiv.swap 0 1 1)) = F.center 0
  rw [Equiv.swap_apply_right]
  rfl

theorem DegreeTwelveFrame.swapCenters_leaf {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (e : Fin 2) :
    F.swapCenters.leaf i e = F.leaf i e := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let z : ↥(neighborColorFiber v c (F.pairIndex i).val) := by
    cases hdec
    exact F.pairVertices i e
  have hF : z.val = F.leaf i e := by
    cases hdec
    rfl
  have hswap : z.val = F.swapCenters.leaf i e := by
    cases hdec
    rfl
  exact hswap.symm.trans hF


theorem DegreeTwelveFrame.leaf_same_pair_not_adj {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (e d : Fin 2) :
    ¬ G.Adj (F.leaf i e).val (F.leaf i d).val := by
  intro he
  have hn : neighborColor v c (F.leaf i e) ≠ neighborColor v c (F.leaf i d) := c.valid he
  exact hn ((F.leaf_color i e).trans (F.leaf_color i d).symm)


theorem DegreeTwelveFrame.color_cases {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (k : Fin 7) :
    (∃ j : Fin 2, (F.singletonIndex j).val = k) ∨
      ∃ i : Fin 5, (F.pairIndex i).val = k := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  have hset : singletonNeighborColors v c =
      @singletonNeighborColors V (inferInstance : Fintype V) G
        (fun a b => Classical.propDecidable (G.Adj a b)) v c := by
    cases hdec
    rfl
  classical
  by_cases hk : k ∈ singletonNeighborColors v c
  · have hk' : k ∈ @singletonNeighborColors V (inferInstance : Fintype V) G
        (fun a b => Classical.propDecidable (G.Adj a b)) v c := by
      rw [← hset]
      exact hk
    obtain ⟨j, hj⟩ := F.singletonIndex.surjective ⟨k, hk'⟩
    exact Or.inl ⟨j, congrArg Subtype.val hj⟩
  · have hk' : k ∉ @singletonNeighborColors V (inferInstance : Fintype V) G
        (fun a b => Classical.propDecidable (G.Adj a b)) v c := by
      rw [← hset]
      exact hk
    obtain ⟨i, hi⟩ := F.pairIndex.surjective ⟨k, Finset.mem_compl.mpr hk'⟩
    exact Or.inr ⟨i, congrArg Subtype.val hi⟩

noncomputable def DegreeTwelveFrame.commonRep {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) : G.neighborSet v :=
  F.leaf i.val (Classical.choose (Finset.mem_filter.mp i.property).2)

theorem DegreeTwelveFrame.commonRep_adj_zero {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    G.Adj (F.center 0).val (F.commonRep i).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  exact (Classical.choose_spec (Finset.mem_filter.mp i.property).2).1

theorem DegreeTwelveFrame.commonRep_adj_one {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    G.Adj (F.center 1).val (F.commonRep i).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  exact (Classical.choose_spec (Finset.mem_filter.mp i.property).2).2

theorem DegreeTwelveFrame.commonRep_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    neighborColor v c (F.commonRep i) = (F.pairIndex i.val).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  exact F.leaf_color i.val _


end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame
#print axioms TaskH.Seven.DegreeTwelveFrame.center
#print axioms TaskH.Seven.DegreeTwelveFrame.leaf
#print axioms TaskH.Seven.equality_degreeTwelveFrame
#print axioms TaskH.Seven.DegreeTwelveFrame.center_color
#print axioms TaskH.Seven.DegreeTwelveFrame.leaf_color
#print axioms TaskH.Seven.DegreeTwelveFrame.leaf_same_pair_injective
#print axioms TaskH.Seven.DegreeTwelveFrame.center_center_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.center_leaf_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.leaf_leaf_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.neighbor_cases
#print axioms TaskH.Seven.DegreeTwelveFrame.commonColors
#print axioms TaskH.Seven.DegreeTwelveFrame.IsPureSplit
#print axioms TaskH.Seven.DegreeTwelveFrame.center_meets_pair
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_iff_commonColors_empty

#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_center_zero
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_center_one
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_leaf

#print axioms TaskH.Seven.DegreeTwelveFrame.leaf_same_pair_not_adj

#print axioms TaskH.Seven.DegreeTwelveFrame.color_cases
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep_adj_zero
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep_adj_one
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep_color
