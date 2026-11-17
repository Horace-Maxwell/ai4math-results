import Research.TaskH.Seven.SevenAttachmentData

/-! Original-graph transport of the seven-index replacement obstruction. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

open scoped Classical in
theorem rainbow_heptagon_neighbors_card_le_four [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (f : Fin 7 → V) (hf : IsHeptagon G f)
    (y : V) (hyout : ∀ i, y ≠ f i) :
    ((G.neighborFinset y).filter (fun x => CycleContains (heptagonEdges f) x)).card ≤ 4 := by
  classical
  let S : Finset V := insert y (Finset.univ.image f)
  have him : (Finset.univ.image f).card ≤ 7 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin 7))) (f := f))
  have hS : S.card ≤ 8 := by
    have hh := Finset.card_insert_le y (Finset.univ.image f)
    change (insert y (Finset.univ.image f)).card ≤ 8
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
  let F : Fin 7 → {x : V // x ≠ w} := fun i => ⟨f i, hfw i⟩
  let d : Fin 7 → Fin 7 := fun i => c (F i)
  let p := heptagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1
    hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2
  have hp : p.IsCycle := heptagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2
  have hfin : ∀ i, f i ∈ p.support := heptagon_walk_support f hf
  have hdinj : Function.Injective d := by
    intro i j hij
    apply hf.1
    have he := hr w c p hp (by rfl) (F i) (F j) (hfin i) (hfin j) hij
    exact congrArg Subtype.val he
  obtain ⟨q, hq⟩ := Finite.surjective_of_injective hdinj (c ⟨y, hyw⟩)
  have hcolor : c ⟨y, hyw⟩ = c ⟨f q, hfw q⟩ := hq.symm
  let A : Finset (Fin 7) := Finset.univ.filter (fun i => G.Adj y (f i))
  have hreplace : ∀ i : Fin 7, i + 6 ∈ A → i + 1 ∈ A → i = q := by
    intro i hip hin
    by_contra hiq
    have hqi : q ≠ i := Ne.symm hiq
    let g := heptagonReplace f y i
    have hg : IsHeptagon G g := heptagonReplace_isHeptagon f hf y hyout i
      (Finset.mem_filter.mp hip).2 (Finset.mem_filter.mp hin).2
    let r := heptagonWalk G g hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2
    have hrc : r.IsCycle := heptagonWalk_isCycle G g hg.1 hg.2.1 hg.2.2.1
      hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2
    have hgi : g i = y := by simp only [g, heptagonReplace, ite_true]
    have hgq : g q = f q := by simp only [g, heptagonReplace, ite_eq_right hqi]
    have hwi : g i ≠ w := by simpa only [hgi] using hyw
    have hwq : g q ≠ w := by simpa only [hgq] using hfw q
    have he : c ⟨g i, hwi⟩ = c ⟨g q, hwq⟩ := by
      simpa only [hgi, hgq] using hcolor
    have hh := hr w c r hrc (by rfl) ⟨g i, hwi⟩ ⟨g q, hwq⟩
      (heptagon_walk_support g hg i) (heptagon_walk_support g hg q) he
    have hval := congrArg Subtype.val hh
    exact hyout q (by simpa only [hgi, hgq] using hval)
  have hAc : A.card ≤ 4 := seven_index_replacement_bound A q hreplace
  have himage :
      (G.neighborFinset y).filter (fun x => CycleContains (heptagonEdges f) x) =
        A.image f := by
    ext x
    simp only [Finset.mem_filter, G.mem_neighborFinset,
      cycleContains_heptagonEdges_iff, Finset.mem_image]
    constructor
    · rintro ⟨hyx, i, rfl⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Finset.mem_filter.mp hi).2, i, rfl⟩
  rw [himage, Finset.card_image_of_injective _ hf.1]
  exact hAc

open scoped Classical in
theorem outside_cycle_neighbors_card_le_four [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G)
    (hr : RainbowSevenCycles G) (hn : 9 ≤ Fintype.card V)
    (s : Finset (Sym2 V)) (hmem : s ∈ ModCycleEdgeSets 7 G)
    (y : V) (hy : ¬ CycleContains s y) :
    ((G.neighborFinset y).filter (fun x => CycleContains s x)).card ≤ 4 := by
  classical
  obtain ⟨a, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_heptagon_of_cycle_length_seven hp hl
  have hyout : ∀ i, y ≠ f i := by
    intro i hiy
    apply hy
    rw [← he, ← hfe]
    exact (cycleContains_heptagonEdges_iff f y).mpr ⟨i, hiy.symm⟩
  have hbound := rainbow_heptagon_neighbors_card_le_four hcrit hr hn f hf y hyout
  simpa only [hfe, he] using hbound

end TaskH.Seven

#print axioms TaskH.Seven.rainbow_heptagon_neighbors_card_le_four
#print axioms TaskH.Seven.outside_cycle_neighbors_card_le_four
