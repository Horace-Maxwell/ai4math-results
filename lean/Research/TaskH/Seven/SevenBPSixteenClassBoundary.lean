import Research.TaskH.Seven.SevenBPCycleAttachments
import Research.TaskH.Seven.SevenBPInternalEdges

/-! The eight genuine vertices in each C16 color class and their actual
internal-edge and outside-neighbor counts. Adapted from the explicitly
preserved C18 class-boundary source, with the C16 bounds proved here. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def sixteenAttachmentClassIndex (q : Fin 2) (i : Fin 8) : Fin 16 := finProdFinEquiv (i,q)

noncomputable def sixteenAttachmentClassHooks (G : SimpleGraph V) (u : Fin 16 → V)
    (z : V) (q : Fin 2) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => G.Adj z (u (sixteenAttachmentClassIndex q i)))

theorem sixteenAttachmentClassIndex_injective (q : Fin 2) : Function.Injective (sixteenAttachmentClassIndex q) := by
  intro i j he
  exact congrArg Prod.fst (finProdFinEquiv.injective he)

theorem sixteenAttachment_class_zero_color (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (i : Fin 8) : c (u (sixteenAttachmentClassIndex 0 i))=c (u 0) := by
  have hc := cycle_sixteen_color_even_iff u hu c (sixteenAttachmentClassIndex 0 i)
  have hi : Even (sixteenAttachmentClassIndex 0 i).val := by
    rw [Nat.even_iff]
    have tab : ∀ i : Fin 8, (sixteenAttachmentClassIndex 0 i).val%2=0 := by decide +kernel
    exact tab i
  have hh := hc.mp hi
  cases h0 : c (u 0) <;> cases h1 : c (u (sixteenAttachmentClassIndex 0 i)) <;> simp_all

theorem sixteenAttachment_class_one_color_ne (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (i : Fin 8) : c (u (sixteenAttachmentClassIndex 1 i))≠c (u 0) := by
  have hc := cycle_sixteen_color_even_iff u hu c (sixteenAttachmentClassIndex 1 i)
  have hi : ¬Even (sixteenAttachmentClassIndex 1 i).val := by
    rw [Nat.even_iff]
    have tab : ∀ i : Fin 8, (sixteenAttachmentClassIndex 1 i).val%2≠0 := by decide +kernel
    exact tab i
  intro he
  apply hi
  apply hc.mpr
  rw [he]

theorem sixteenAttachment_same_class_not_adj (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (q : Fin 2) (i j : Fin 8) :
    ¬G.Adj (u (sixteenAttachmentClassIndex q i)) (u (sixteenAttachmentClassIndex q j)) := by
  intro ha
  have hn := c.valid ha
  fin_cases q
  · change c (u (sixteenAttachmentClassIndex 0 i)) ≠
      c (u (sixteenAttachmentClassIndex 0 j)) at hn
    rw [sixteenAttachment_class_zero_color u hu c i,sixteenAttachment_class_zero_color u hu c j] at hn
    exact hn rfl
  · change c (u (sixteenAttachmentClassIndex 1 i)) ≠
      c (u (sixteenAttachmentClassIndex 1 j)) at hn
    have hi := sixteenAttachment_class_one_color_ne u hu c i
    have hj := sixteenAttachment_class_one_color_ne u hu c j
    cases h0 : c (u 0) <;> cases h1 : c (u (sixteenAttachmentClassIndex 1 i)) <;>
      cases h2 : c (u (sixteenAttachmentClassIndex 1 j)) <;> simp_all

noncomputable def sixteenAttachmentCycleEdges (u : Fin 16 → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin 16 => s(u i,u (i+1)))

noncomputable def sixteenAttachmentClassInternalPairs (G : SimpleGraph V) (u : Fin 16 → V) (q : Fin 2) :
    Finset (Fin 8 × Fin 16) := Finset.univ.filter
      (fun p => G.Adj (u (sixteenAttachmentClassIndex q p.1)) (u p.2))

theorem sixteenAttachment_class_internal_edge_injOn (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) :
    Set.InjOn (fun p : Fin 8 × Fin 16 => s(u (sixteenAttachmentClassIndex q p.1),u p.2))
      (sixteenAttachmentClassInternalPairs G u q) := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  intro p hp r hr he
  have hidx : s(sixteenAttachmentClassIndex q p.1,p.2)=s(sixteenAttachmentClassIndex q r.1,r.2) := by
    apply Sym2.map.injective hu.1
    simpa using he
  have hi : (sixteenAttachmentClassIndex q p.1=sixteenAttachmentClassIndex q r.1 ∧ p.2=r.2) ∨
      (sixteenAttachmentClassIndex q p.1=r.2 ∧ p.2=sixteenAttachmentClassIndex q r.1) := by
    simpa only [Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] using hidx
  rcases hi with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext (sixteenAttachmentClassIndex_injective q h1) h2
  · have ha := (Finset.mem_filter.mp hp).2
    exact False.elim (sixteenAttachment_same_class_not_adj u hu c q p.1 r.1 (by simpa only [h2] using ha))

theorem sixteenAttachment_class_internal_pairs_card_le_twenty_seven (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (u : Fin 16 → V) (hu : IsCycleSixteen G u) (q : Fin 2) :
    (sixteenAttachmentClassInternalPairs G u q).card ≤ 27 := by
  let f : Fin 8 × Fin 16 → Sym2 V := fun p => s(u (sixteenAttachmentClassIndex q p.1),u p.2)
  have him : (sixteenAttachmentClassInternalPairs G u q).image f ⊆ actualInternalEdges G u := by
    intro e he
    obtain ⟨⟨i,j⟩,hp,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨(sixteenAttachmentClassIndex q i,j),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩,rfl⟩
  have hcard : ((sixteenAttachmentClassInternalPairs G u q).image f).card =
      (sixteenAttachmentClassInternalPairs G u q).card :=
    Finset.card_image_of_injOn (sixteenAttachment_class_internal_edge_injOn hb u hu q)
  have hle := Finset.card_le_card him
  have hi := actualInternalEdges_card u hu
  have hc := actualChordEdges_card_le_eleven hb u hu h14
  omega

theorem sixteenAttachment_class_internal_pairs_eq_sum [Fintype V]
    (u : Fin 16 → V) (hu : Function.Injective u) (q : Fin 2) :
    (sixteenAttachmentClassInternalPairs G u q).card =
      ∑ i : Fin 8,(G.neighborFinset (u (sixteenAttachmentClassIndex q i)) ∩ Finset.univ.image u).card := by
  simp only [sixteenAttachmentClassInternalPairs,Finset.card_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [actual_cycle_neighbor_card u hu]
  simp only [outsideHookFinset,Finset.card_filter]

theorem sixteenAttachment_cycle_class_external_edges_ge_twenty_nine [Fintype V]
    (hb : G.IsBipartite) (h14 : NoFourteenCycle G)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hd : ∀ x : V,7≤G.degree x) (q : Fin 2) :
    29 ≤ ∑ i : Fin 8,(G.neighborFinset (u (sixteenAttachmentClassIndex q i)) \ Finset.univ.image u).card := by
  have hi := sixteenAttachment_class_internal_pairs_card_le_twenty_seven hb h14 u hu q
  rw [sixteenAttachment_class_internal_pairs_eq_sum u hu.1 q] at hi
  have hdeg : 56 ≤ ∑ i : Fin 8,G.degree (u (sixteenAttachmentClassIndex q i)) := by
    calc
      56 = ∑ _i : Fin 8,(7 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hd (u (sixteenAttachmentClassIndex q i)))
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 8))) rfl
    (fun i _ => boundary_degree_partition (G:=G) (Finset.univ.image u) (u (sixteenAttachmentClassIndex q i)))
  rw [Finset.sum_add_distrib] at hsum
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.sixteenAttachmentClassIndex
#print axioms TaskH.Seven.BP.sixteenAttachmentClassHooks
#print axioms TaskH.Seven.BP.sixteenAttachmentClassIndex_injective
#print axioms TaskH.Seven.BP.sixteenAttachment_class_zero_color
#print axioms TaskH.Seven.BP.sixteenAttachment_class_one_color_ne
#print axioms TaskH.Seven.BP.sixteenAttachment_same_class_not_adj
#print axioms TaskH.Seven.BP.sixteenAttachmentCycleEdges
#print axioms TaskH.Seven.BP.sixteenAttachmentClassInternalPairs
#print axioms TaskH.Seven.BP.sixteenAttachment_class_internal_edge_injOn
#print axioms TaskH.Seven.BP.sixteenAttachment_class_internal_pairs_card_le_twenty_seven
#print axioms TaskH.Seven.BP.sixteenAttachment_class_internal_pairs_eq_sum
#print axioms TaskH.Seven.BP.sixteenAttachment_cycle_class_external_edges_ge_twenty_nine
