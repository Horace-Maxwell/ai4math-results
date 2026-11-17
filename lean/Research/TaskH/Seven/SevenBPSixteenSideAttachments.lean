import Research.TaskH.Seven.SevenBPSixteenClassBoundary

/-! The actual outside sides and their attachment sums. The lower bound29
is transported from the eight actual cycle vertices by a true relation count. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem sixteenAttachment_class_colors_eq (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (q : Fin 2) (i j : Fin 8) :
    c (u (sixteenAttachmentClassIndex q i))=c (u (sixteenAttachmentClassIndex q j)) := by
  fin_cases q
  · change c (u (sixteenAttachmentClassIndex 0 i)) =
      c (u (sixteenAttachmentClassIndex 0 j))
    rw [sixteenAttachment_class_zero_color u hu c i,sixteenAttachment_class_zero_color u hu c j]
  · change c (u (sixteenAttachmentClassIndex 1 i)) =
      c (u (sixteenAttachmentClassIndex 1 j))
    have hi := sixteenAttachment_class_one_color_ne u hu c i
    have hj := sixteenAttachment_class_one_color_ne u hu c j
    cases h0 : c (u 0) <;> cases h1 : c (u (sixteenAttachmentClassIndex 1 i)) <;>
      cases h2 : c (u (sixteenAttachmentClassIndex 1 j)) <;> simp_all

theorem sixteenAttachment_class_colors_ne (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (q r : Fin 2) (hqr : q≠r) (i j : Fin 8) :
    c (u (sixteenAttachmentClassIndex q i))≠c (u (sixteenAttachmentClassIndex r j)) := by
  fin_cases q <;> fin_cases r
  · exact (hqr rfl).elim
  · change c (u (sixteenAttachmentClassIndex 0 i)) ≠
      c (u (sixteenAttachmentClassIndex 1 j))
    rw [sixteenAttachment_class_zero_color u hu c i]
    exact (sixteenAttachment_class_one_color_ne u hu c j).symm
  · change c (u (sixteenAttachmentClassIndex 1 i)) ≠
      c (u (sixteenAttachmentClassIndex 0 j))
    rw [sixteenAttachment_class_zero_color u hu c j]
    exact sixteenAttachment_class_one_color_ne u hu c i
  · exact (hqr rfl).elim

noncomputable def sixteenAttachmentOutsideSide [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (q : Fin 2) : Finset V :=
  (Finset.univ \ Finset.univ.image u).filter
    (fun z => c z≠c (u (sixteenAttachmentClassIndex q 0)))

theorem sixteenAttachment_outside_neighbor_in_side [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) (i : Fin 8) (z : V)
    (hz : z∉Finset.univ.image u) (ha : G.Adj (u (sixteenAttachmentClassIndex q i)) z) :
    z∈sixteenAttachmentOutsideSide c u q := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩,?_⟩
  intro he
  apply c.valid ha
  exact (sixteenAttachment_class_colors_eq u hu c q i 0).trans he.symm

theorem sixteenAttachment_side_hook_image [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) (z : V)
    (hz : z∈sixteenAttachmentOutsideSide c u q) :
    outsideHookFinset G u z=(sixteenAttachmentClassHooks G u z q).image (sixteenAttachmentClassIndex q) := by
  ext j
  constructor
  · intro hj
    let p : Fin 8 × Fin 2 := finProdFinEquiv.symm j
    have hp : sixteenAttachmentClassIndex p.2 p.1=j := by
      change (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin (8 * 2))
        ((finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin (8 * 2)).symm j) = j
      exact (finProdFinEquiv : Fin 8 × Fin 2 ≃ Fin (8 * 2)).apply_symm_apply j
    have hrq : p.2=q := by
      by_contra hne
      have hcn := sixteenAttachment_class_colors_ne u hu c p.2 q hne p.1 0
      have hzn : c z≠c (u (sixteenAttachmentClassIndex p.2 p.1)) := by
        apply c.valid
        simpa only [hp] using (Finset.mem_filter.mp hj).2
      have hzq := (Finset.mem_filter.mp hz).2
      cases hz' : c z <;> cases hr' : c (u (sixteenAttachmentClassIndex p.2 p.1)) <;>
        cases hq' : c (u (sixteenAttachmentClassIndex q 0)) <;> simp_all
    have he : sixteenAttachmentClassIndex q p.1=j := by simpa only [hrq] using hp
    exact Finset.mem_image.mpr ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa only [he] using (Finset.mem_filter.mp hj).2⟩,he⟩
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

theorem sixteenAttachment_side_hook_card [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) (z : V)
    (hz : z∈sixteenAttachmentOutsideSide c u q) :
    (outsideHookFinset G u z).card=(sixteenAttachmentClassHooks G u z q).card := by
  rw [sixteenAttachment_side_hook_image c u hu q z hz,
    Finset.card_image_of_injective _ (sixteenAttachmentClassIndex_injective q)]

theorem sixteenAttachment_outside_side_attachment_count [Fintype V] (c : G.Coloring Bool)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) :
    (∑ i : Fin 8,(G.neighborFinset (u (sixteenAttachmentClassIndex q i)) \ Finset.univ.image u).card)=
      ∑ z∈sixteenAttachmentOutsideSide c u q,(outsideHookFinset G u z).card := by
  let S := sixteenAttachmentOutsideSide c u q
  let R : Fin 8 → V → Prop := fun i z => G.Adj (u (sixteenAttachmentClassIndex q i)) z
  have hrow (i : Fin 8) : S.filter (R i)=
      G.neighborFinset (u (sixteenAttachmentClassIndex q i)) \ Finset.univ.image u := by
    ext z
    constructor
    · intro hz
      have hzs := (Finset.mem_filter.mp hz).1
      have ha := (Finset.mem_filter.mp hz).2
      exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ha,
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzs).1).2⟩
    · intro hz
      have ha := (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1
      have hzs := sixteenAttachment_outside_neighbor_in_side c u hu q i z (Finset.mem_sdiff.mp hz).2 ha
      exact Finset.mem_filter.mpr ⟨hzs,ha⟩
  have hcol (z : V) : (Finset.univ : Finset (Fin 8)).filter (fun i => R i z)=
      sixteenAttachmentClassHooks G u z q := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,sixteenAttachmentClassHooks]
    exact ⟨fun h=>h.symm,fun h=>h.symm⟩
  calc
    _ = ∑ i : Fin 8,(S.filter (R i)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow]
    _ = ∑ z∈S,((Finset.univ : Finset (Fin 8)).filter (fun i=>R i z)).card :=
      FiniteBudget.relation_double_count Finset.univ S R
    _ = ∑ z∈S,(outsideHookFinset G u z).card := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hcol,←sixteenAttachment_side_hook_card c u hu q z hz]

theorem sixteenAttachment_each_side_attachments_ge_twenty_nine [Fintype V]
    (hb : G.IsBipartite) (h14 : NoFourteenCycle G)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hd : ∀ x : V,7≤G.degree x)
    (c : G.Coloring Bool) (q : Fin 2) :
    29 ≤ ∑ z∈sixteenAttachmentOutsideSide c u q,(outsideHookFinset G u z).card := by
  have hh := sixteenAttachment_cycle_class_external_edges_ge_twenty_nine hb h14 u hu hd q
  rw [sixteenAttachment_outside_side_attachment_count c u hu q] at hh
  exact hh

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.sixteenAttachment_class_colors_eq
#print axioms TaskH.Seven.BP.sixteenAttachment_class_colors_ne
#print axioms TaskH.Seven.BP.sixteenAttachmentOutsideSide
#print axioms TaskH.Seven.BP.sixteenAttachment_outside_neighbor_in_side
#print axioms TaskH.Seven.BP.sixteenAttachment_side_hook_image
#print axioms TaskH.Seven.BP.sixteenAttachment_side_hook_card
#print axioms TaskH.Seven.BP.sixteenAttachment_outside_side_attachment_count
#print axioms TaskH.Seven.BP.sixteenAttachment_each_side_attachments_ge_twenty_nine
