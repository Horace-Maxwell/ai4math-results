import Research.TaskH.Six.SixAttachmentData

/-!
Actual graph transport of the six-position obstruction. The extra deleted
vertex is chosen outside the given real hexagon and its outside point;
R then forces at most three actual hexagon neighbors.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

open scoped Classical in
theorem rainbow_hexagon_neighbors_card_le_three [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (f : Fin 6 → V) (hf : IsHexagon G f)
    (y : V) (hyout : ∀ i, y ≠ f i) :
    ((G.neighborFinset y).filter (fun x => CycleContains (hexagonEdges f) x)).card ≤ 3 := by
  classical
  let S : Finset V := insert y (Finset.univ.image f)
  have him : (Finset.univ.image f).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin 6))) (f := f))
  have hS : S.card ≤ 7 := by
    have hh := Finset.card_insert_le y (Finset.univ.image f)
    change (insert y (Finset.univ.image f)).card ≤ 7
    omega
  have hlt : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hyS : y ∈ S := Finset.mem_insert_self _ _
  have hyw : y ≠ w := fun he => hw (he ▸ hyS)
  have hfw : ∀ i, f i ≠ w := by
    intro i he
    apply hw
    rw [← he]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  let F : Fin 6 → {x : V // x ≠ w} := fun i => ⟨f i, hfw i⟩
  let d : Fin 6 → Fin 6 := fun i => c (F i)
  let p := hexagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hp : p.IsCycle := hexagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2
  have hfin : ∀ i, f i ∈ p.support := by
    intro i
    fin_cases i <;> simp [p, hexagonWalk, Walk.support_cons]
  have hdinj : Function.Injective d := by
    intro i j hij
    apply hf.1
    have he := hr w c p hp (by rfl) (F i) (F j) (hfin i) (hfin j) hij
    exact congrArg Subtype.val he
  obtain ⟨q, hq⟩ := Finite.surjective_of_injective hdinj (c ⟨y, hyw⟩)
  have hcolor : c ⟨y, hyw⟩ = c ⟨f q, hfw q⟩ := hq.symm
  let A : Finset (Fin 6) := Finset.univ.filter (fun i => G.Adj y (f i))
  have hqA : q ∉ A := by
    intro hmem
    have ha := (Finset.mem_filter.mp hmem).2
    have ha' : (G.induce {x | x ≠ w}).Adj ⟨y, hyw⟩ ⟨f q, hfw q⟩ := ha
    exact (c.valid ha') hcolor
  have h13 : ¬ (q + 1 ∈ A ∧ q + 3 ∈ A) := by
    rintro ⟨h1, h3⟩
    let t := f ∘ firstForbiddenPath q
    have ht : Function.Injective t := hf.1.comp (firstForbiddenPath_injective q)
    have hadj := firstForbiddenPath_adj hf q
    have hwt : ∀ i, t i ≠ w := fun i => hfw (firstForbiddenPath q i)
    have hout : ∀ i, y ≠ t i := fun i => hyout (firstForbiddenPath q i)
    have hc : c ⟨y, hyw⟩ = c ⟨t 1, hwt 1⟩ := hcolor
    apply rainbow_forbids_four_path hr w c t ht hadj.1 hadj.2.1 hadj.2.2.1 hadj.2.2.2
      y hyw hwt hout 1 hc
    exact ⟨(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h3).2⟩
  have h24 : ¬ (q + 2 ∈ A ∧ q + 4 ∈ A) := by
    rintro ⟨h2, h4⟩
    let t := f ∘ secondForbiddenPath q
    have ht : Function.Injective t := hf.1.comp (secondForbiddenPath_injective q)
    have hadj := secondForbiddenPath_adj hf q
    have hwt : ∀ i, t i ≠ w := fun i => hfw (secondForbiddenPath q i)
    have hout : ∀ i, y ≠ t i := fun i => hyout (secondForbiddenPath q i)
    have hc : c ⟨y, hyw⟩ = c ⟨t 2, hwt 2⟩ := hcolor
    apply rainbow_forbids_four_path hr w c t ht hadj.1 hadj.2.1 hadj.2.2.1 hadj.2.2.2
      y hyw hwt hout 2 hc
    exact ⟨(Finset.mem_filter.mp h2).2, (Finset.mem_filter.mp h4).2⟩
  have h35 : ¬ (q + 3 ∈ A ∧ q + 5 ∈ A) := by
    rintro ⟨h3, h5⟩
    let t := f ∘ thirdForbiddenPath q
    have ht : Function.Injective t := hf.1.comp (thirdForbiddenPath_injective q)
    have hadj := thirdForbiddenPath_adj hf q
    have hwt : ∀ i, t i ≠ w := fun i => hfw (thirdForbiddenPath q i)
    have hout : ∀ i, y ≠ t i := fun i => hyout (thirdForbiddenPath q i)
    have hc : c ⟨y, hyw⟩ = c ⟨t 3, hwt 3⟩ := hcolor
    apply rainbow_forbids_four_path hr w c t ht hadj.1 hadj.2.1 hadj.2.2.1 hadj.2.2.2
      y hyw hwt hout 3 hc
    exact ⟨(Finset.mem_filter.mp h3).2, (Finset.mem_filter.mp h5).2⟩
  have hAc : A.card ≤ 3 := six_index_neighbor_bound A q hqA h13 h24 h35
  have himage :
      (G.neighborFinset y).filter (fun x => CycleContains (hexagonEdges f) x) =
        A.image f := by
    ext x
    simp only [Finset.mem_filter, G.mem_neighborFinset,
      cycleContains_hexagonEdges_iff, Finset.mem_image]
    constructor
    · rintro ⟨hyx, i, rfl⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Finset.mem_filter.mp hi).2, i, rfl⟩
  rw [himage, Finset.card_image_of_injective _ hf.1]
  exact hAc

open scoped Classical in
theorem outside_cycle_neighbors_card_le_three [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G)
    (hr : RainbowSixCycles G) (hn : 8 ≤ Fintype.card V)
    (s : Finset (Sym2 V)) (hmem : s ∈ ModCycleEdgeSets 6 G)
    (y : V) (hy : ¬ CycleContains s y) :
    ((G.neighborFinset y).filter (fun x => CycleContains s x)).card ≤ 3 := by
  classical
  obtain ⟨a, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_hexagon_of_cycle_length_six hp hl
  have hyout : ∀ i, y ≠ f i := by
    intro i hiy
    apply hy
    rw [← he, ← hfe]
    exact (cycleContains_hexagonEdges_iff f y).mpr ⟨i, hiy.symm⟩
  have hbound := rainbow_hexagon_neighbors_card_le_three hcrit hr hn f hf y hyout
  simpa only [hfe, he] using hbound

end TaskH.Six

#print axioms TaskH.Six.rainbow_hexagon_neighbors_card_le_three
#print axioms TaskH.Six.outside_cycle_neighbors_card_le_three
