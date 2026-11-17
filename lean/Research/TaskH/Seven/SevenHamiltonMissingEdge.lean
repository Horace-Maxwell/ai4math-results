import Research.TaskH.Seven.SevenHamiltonCoordinates

/-! Actual seven-point circle edge sets in an actual graph missing an
actual edge are encoded by the480 allowed rooted oriented permutations. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def sevenVertexCircleFinset (G : SimpleGraph V) (Q : Finset V) :
    Finset (Finset (Sym2 V)) :=
  (actualSevenEdgeSets G).filter (fun C => TaskH.cycleVertices C ⊆ Q)

theorem sevenVertexCircle_rooted_word {Q : Finset V} (hQ : Q.card = 7)
    {u : V} (hu : u ∈ Q) {C : Finset (Sym2 V)}
    (hC : C ∈ sevenVertexCircleFinset G Q) :
    ∃ f : Fin 7 → V, IsHeptagon G f ∧ f 0 = u ∧
      (∀ i : Fin 7, f i ∈ Q) ∧ heptagonEdges f = C := by
  classical
  obtain ⟨f, hf, hset⟩ :=
    (mem_actualSevenEdgeSets_iff C).mp (Finset.mem_filter.mp hC).1
  have hfQ : ∀ i : Fin 7, f i ∈ Q := by
    intro i
    apply (Finset.mem_filter.mp hC).2
    apply (TaskH.mem_cycleVertices C (f i)).mpr
    rw [← hset]
    exact (cycleContains_heptagonEdges_iff f (f i)).mpr ⟨i, rfl⟩
  have himage : Finset.univ.image f = Q := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
      exact hfQ i
    · rw [Finset.card_image_of_injective _ hf.1, Finset.card_univ, Fintype.card_fin, hQ]
  have huimage : u ∈ Finset.univ.image f := by rw [himage]; exact hu
  obtain ⟨i, _hi, hiu⟩ := Finset.mem_image.mp huimage
  refine ⟨f ∘ heptagonOrientedIndex false i, isHeptagon_reindex f hf (false, i), ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, heptagonOrientedIndex_zero] using hiu
  · intro j
    exact hfQ (heptagonOrientedIndex false i j)
  · exact (heptagonEdges_reindex f (false, i)).trans hset

/-- Both orientations are explicitly constructed and encoded. Their
different permutation parameters follow from genuine word injectivity. -/
theorem actual_circle_two_rooted_parameters {Q : Finset V} (hQ : Q.card = 7)
    (e : Q ≃ Fin 7) {u v : V} (huQ : u ∈ Q)
    (hu : (e.symm 0).val = u) (a : Fin 6) (hv : (e.symm a.succ).val = v)
    (hnon : ¬ G.Adj u v) {C : Finset (Sym2 V)}
    (hC : C ∈ sevenVertexCircleFinset G Q) :
    2 ≤ ((hamiltonAvoidingEnds 0 5 a).filter
      (fun π => heptagonEdges (rootedHamiltonWord e π) = C)).card := by
  classical
  obtain ⟨f, hf, hf0, hfQ, hfset⟩ := sevenVertexCircle_rooted_word hQ huQ hC
  let g := f ∘ heptagonOrientedIndex true 0
  have hg : IsHeptagon G g := isHeptagon_reindex f hf (true, 0)
  have hg0 : g 0 = u := by
    simpa only [g, Function.comp_apply, heptagonOrientedIndex_zero] using hf0
  have hgQ : ∀ i : Fin 7, g i ∈ Q := fun i => hfQ (heptagonOrientedIndex true 0 i)
  have hgset : heptagonEdges g = C := (heptagonEdges_reindex f (true, 0)).trans hfset
  have hfg : f ≠ g := by
    intro heq
    have hid : f ∘ heptagonOrientedIndex false 0 = f := by
      funext i
      simp [Function.comp_apply, heptagonOrientedIndex]
    have hparam : (false, (0 : Fin 7)) = (true, (0 : Fin 7)) :=
      heptagon_reindex_parameters_injective f hf.1 (hid.trans heq)
    have hbool : false = true := congrArg Prod.fst hparam
    cases hbool
  obtain ⟨π, hπ⟩ := rootedHamiltonWord_encoding e f hf.1 hfQ (hf0.trans hu.symm)
  obtain ⟨ρ, hρ⟩ := rootedHamiltonWord_encoding e g hg.1 hgQ (hg0.trans hu.symm)
  have hπmem : π ∈ hamiltonAvoidingEnds 0 5 a :=
    rootedHamiltonWord_mem_avoiding e hu a hv hnon π (by rw [hπ]; exact hf)
  have hρmem : ρ ∈ hamiltonAvoidingEnds 0 5 a :=
    rootedHamiltonWord_mem_avoiding e hu a hv hnon ρ (by rw [hρ]; exact hg)
  have hπset : heptagonEdges (rootedHamiltonWord e π) = C := by rw [hπ]; exact hfset
  have hρset : heptagonEdges (rootedHamiltonWord e ρ) = C := by rw [hρ]; exact hgset
  have hne : π ≠ ρ := by
    intro heq
    exact hfg (hπ.symm.trans ((congrArg (rootedHamiltonWord e) heq).trans hρ))
  have hsub : ({π, ρ} : Finset (Equiv.Perm (Fin 6))) ⊆
      (hamiltonAvoidingEnds 0 5 a).filter
        (fun τ => heptagonEdges (rootedHamiltonWord e τ) = C) := by
    intro τ hτ
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact Finset.mem_filter.mpr ⟨hπmem, hπset⟩
    · have hτ' := Finset.mem_singleton.mp hτ
      subst τ
      exact Finset.mem_filter.mpr ⟨hρmem, hρset⟩
  have hle := Finset.card_le_card hsub
  simpa only [Finset.card_pair hne] using hle

/-- Every actual C7 contained in seven actual vertices of G is counted;
no circle coverage or numerical capacity is supplied as a premise. -/
theorem sevenVertexCircleFinset_card_le_240 {Q : Finset V} (hQ : Q.card = 7)
    {u v : V} (huQ : u ∈ Q) (hvQ : v ∈ Q) (hne : u ≠ v)
    (hnon : ¬ G.Adj u v) : (sevenVertexCircleFinset G Q).card ≤ 240 := by
  classical
  let uQ : Q := ⟨u, huQ⟩
  let vQ : Q := ⟨v, hvQ⟩
  let e0 : Q ≃ Fin 7 := Q.equivFinOfCardEq hQ
  let e : Q ≃ Fin 7 := e0.trans (Equiv.swap (e0 uQ) 0)
  have he0 : e uQ = 0 := by simp [e]
  have hu : (e.symm 0).val = u := by
    have h := e.symm_apply_apply uQ
    rw [he0] at h
    exact congrArg Subtype.val h
  have hv0 : e vQ ≠ 0 := by
    intro h
    have hvu : vQ = uQ := e.injective (h.trans he0.symm)
    exact hne (congrArg Subtype.val hvu).symm
  let a : Fin 6 := (e vQ).pred hv0
  have hv : (e.symm a.succ).val = v := by
    change (e.symm ((e vQ).pred hv0).succ).val = v
    rw [Fin.succ_pred]
    exact congrArg Subtype.val (e.symm_apply_apply vQ)
  apply hamilton_two_directions_bound (sevenVertexCircleFinset G Q)
    (hamiltonAvoidingEnds 0 5 a) (fun C π => heptagonEdges (rootedHamiltonWord e π) = C)
  · exact le_of_eq (hamiltonAvoidingEnds_card 0 5 a (by decide))
  · intro C hC
    have hrow : 2 ≤ ((hamiltonAvoidingEnds 0 5 a).filter
        (fun π => heptagonEdges (rootedHamiltonWord e π) = C)).card :=
      actual_circle_two_rooted_parameters hQ e huQ hu a hv hnon hC
    have hfilter :
        @Finset.filter (Equiv.Perm (Fin 6))
          (fun π => heptagonEdges (rootedHamiltonWord e π) = C)
          (fun π => Classical.propDecidable (heptagonEdges (rootedHamiltonWord e π) = C))
          (hamiltonAvoidingEnds 0 5 a) =
        (hamiltonAvoidingEnds 0 5 a).filter
          (fun π => heptagonEdges (rootedHamiltonWord e π) = C) :=
      Finset.filter_congr_decidable _ _ _
    rw [hfilter]
    exact hrow
  · intro π _hπ
    have hfilter :
        @Finset.filter (Finset (Sym2 V))
          (fun C => heptagonEdges (rootedHamiltonWord e π) = C)
          (fun C => Classical.propDecidable (heptagonEdges (rootedHamiltonWord e π) = C))
          (sevenVertexCircleFinset G Q) =
        (sevenVertexCircleFinset G Q).filter
          (fun C => heptagonEdges (rootedHamiltonWord e π) = C) :=
      Finset.filter_congr_decidable _ _ _
    rw [hfilter]
    apply Finset.card_le_one.mpr
    intro C hC D hD
    exact (Finset.mem_filter.mp hC).2.symm.trans (Finset.mem_filter.mp hD).2

end TaskH.Seven

#print axioms TaskH.Seven.sevenVertexCircleFinset
#print axioms TaskH.Seven.sevenVertexCircle_rooted_word
#print axioms TaskH.Seven.actual_circle_two_rooted_parameters
#print axioms TaskH.Seven.sevenVertexCircleFinset_card_le_240
