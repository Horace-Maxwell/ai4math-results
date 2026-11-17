import Research.TaskH.Seven.SevenBPEighteenTripleNeighbors

/-! Each genuine nine-vertex C18 color class has at least36 edges to the
outside. Internal incidence is injected into the actual cycle/chord edge sets. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

theorem eighteen_same_class_not_adj (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (c : G.Coloring Bool) (q : Fin 2) (i j : Fin 9) :
    ¬G.Adj (u (eighteenClassIndex q i)) (u (eighteenClassIndex q j)) := by
  intro ha
  have hn := c.valid ha
  have hcases : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide +kernel
  rcases hcases q with hq | hq
  · subst q
    rw [eighteen_class_zero_color u hu c i,eighteen_class_zero_color u hu c j] at hn
    exact hn rfl
  · subst q
    have hi := eighteen_class_one_color_ne u hu c i
    have hj := eighteen_class_one_color_ne u hu c j
    cases h0 : c (u 0) <;> cases h1 : c (u (eighteenClassIndex 1 i)) <;>
      cases h2 : c (u (eighteenClassIndex 1 j)) <;> simp_all

noncomputable def eighteenCycleEdges (u : Fin 18 → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin 18 => s(u i,u (i+1)))

noncomputable def eighteenClassInternalPairs (G : SimpleGraph V) (u : Fin 18 → V) (q : Fin 2) :
    Finset (Fin 9 × Fin 18) := Finset.univ.filter
      (fun p => G.Adj (u (eighteenClassIndex q p.1)) (u p.2))

theorem eighteen_class_internal_edge_injOn (hb : G.IsBipartite)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) :
    Set.InjOn (fun p : Fin 9 × Fin 18 => s(u (eighteenClassIndex q p.1),u p.2))
      (eighteenClassInternalPairs G u q) := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  intro p hp r hr he
  have hidx : s(eighteenClassIndex q p.1,p.2)=s(eighteenClassIndex q r.1,r.2) := by
    apply Sym2.map.injective hu.1
    simpa using he
  have hi : (eighteenClassIndex q p.1=eighteenClassIndex q r.1 ∧ p.2=r.2) ∨
      (eighteenClassIndex q p.1=r.2 ∧ p.2=eighteenClassIndex q r.1) := by
    simpa only [Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] using hidx
  rcases hi with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext (eighteenClassIndex_injective q h1) h2
  · have ha := (Finset.mem_filter.mp hp).2
    exact False.elim (eighteen_same_class_not_adj u hu c q p.1 r.1 (by simpa only [h2] using ha))

theorem eighteen_class_internal_pairs_card_le_twenty_seven (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (q : Fin 2) :
    (eighteenClassInternalPairs G u q).card≤27 := by
  let f : Fin 9 × Fin 18 → Sym2 V := fun p => s(u (eighteenClassIndex q p.1),u p.2)
  have him : (eighteenClassInternalPairs G u q).image f ⊆
      eighteenCycleEdges u ∪ actualEighteenChordEdges G u := by
    intro e he
    obtain ⟨⟨i,j⟩,hp,rfl⟩ := Finset.mem_image.mp he
    have ha := (Finset.mem_filter.mp hp).2
    by_cases hn : j=eighteenClassIndex q i+1
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨eighteenClassIndex q i,Finset.mem_univ _,by rw [hn]⟩
    · by_cases hp' : eighteenClassIndex q i=j+1
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by
          change s(u j,u (j+1)) = s(u (eighteenClassIndex q i),u j)
          rw [hp']
          exact Sym2.eq_swap⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(eighteenClassIndex q i,j),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hn,hp'⟩,rfl⟩
  have hcard : ((eighteenClassInternalPairs G u q).image f).card=
      (eighteenClassInternalPairs G u q).card :=
    Finset.card_image_of_injOn (eighteen_class_internal_edge_injOn hb u hu q)
  have hle := Finset.card_le_card him
  have hunion := Finset.card_union_le (eighteenCycleEdges u) (actualEighteenChordEdges G u)
  have hcycle : (eighteenCycleEdges u).card≤18 := by
    unfold eighteenCycleEdges
    calc
      _ ≤ (Finset.univ : Finset (Fin 18)).card := Finset.card_image_le
      _ = 18 := by simp
  have hchord := actualEighteenChordEdges_card_le_nine hb h14 h16 u hu
  omega

theorem eighteen_class_internal_pairs_eq_sum [Fintype V]
    (u : Fin 18 → V) (hu : Function.Injective u) (q : Fin 2) :
    (eighteenClassInternalPairs G u q).card =
      ∑ i : Fin 9,(G.neighborFinset (u (eighteenClassIndex q i)) ∩ Finset.univ.image u).card := by
  simp only [eighteenClassInternalPairs,Finset.card_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eighteen_actual_cycle_neighbor_card u hu]
  simp only [eighteenOutsideHooks,Finset.card_filter]

theorem eighteen_cycle_class_external_edges_ge_thirty_six [Fintype V]
    (hb : G.IsBipartite) (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (hd : ∀ x : V,7≤G.degree x) (q : Fin 2) :
    36 ≤ ∑ i : Fin 9,(G.neighborFinset (u (eighteenClassIndex q i)) \ Finset.univ.image u).card := by
  have hi := eighteen_class_internal_pairs_card_le_twenty_seven hb h14 h16 u hu q
  rw [eighteen_class_internal_pairs_eq_sum u hu.1 q] at hi
  have hdeg : 63 ≤ ∑ i : Fin 9,G.degree (u (eighteenClassIndex q i)) := by
    calc
      63 = ∑ _i : Fin 9,(7 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hd (u (eighteenClassIndex q i)))
  have hsum : (∑ i : Fin 9,
      ((G.neighborFinset (u (eighteenClassIndex q i)) ∩ Finset.univ.image u).card +
      (G.neighborFinset (u (eighteenClassIndex q i)) \ Finset.univ.image u).card)) =
      ∑ i : Fin 9, G.degree (u (eighteenClassIndex q i)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact boundary_degree_partition (G := G) (Finset.univ.image u)
      (u (eighteenClassIndex q i))
  rw [Finset.sum_add_distrib] at hsum
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteen_same_class_not_adj
#print axioms TaskH.Seven.BP.eighteenCycleEdges
#print axioms TaskH.Seven.BP.eighteenClassInternalPairs
#print axioms TaskH.Seven.BP.eighteen_class_internal_edge_injOn
#print axioms TaskH.Seven.BP.eighteen_class_internal_pairs_card_le_twenty_seven
#print axioms TaskH.Seven.BP.eighteen_class_internal_pairs_eq_sum
#print axioms TaskH.Seven.BP.eighteen_cycle_class_external_edges_ge_thirty_six
