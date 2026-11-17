import Research.TaskH.Seven.SevenBPEighteenChordData

/-! Actual C18 chord sets, with seven-step and antipodal-nine-step coverage.
The symbolic residue injections count at most six plus three indices. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def eighteenNineIndex (i : Fin 9) : Fin 18 := ⟨i.val, by omega⟩

noncomputable def eighteenSevenIndices (G : SimpleGraph V) (u : Fin 18 → V) : Finset (Fin 18) :=
  Finset.univ.filter (fun i => G.Adj (u i) (u (i+7)))
noncomputable def eighteenNineIndices (G : SimpleGraph V) (u : Fin 18 → V) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => G.Adj (u (eighteenNineIndex i)) (u (eighteenNineIndex i+9)))
noncomputable def actualEighteenChordEdges (G : SimpleGraph V) (u : Fin 18 → V) : Finset (Sym2 V) :=
  ((Finset.univ : Finset (Fin 18 × Fin 18)).filter
    (fun p => G.Adj (u p.1) (u p.2) ∧ p.2 ≠ p.1+1 ∧ p.1 ≠ p.2+1)).image
      (fun p => s(u p.1,u p.2))

theorem eighteen_seven_indices_step_six (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (i : Fin 18) (hi : i ∈ eighteenSevenIndices G u) :
    i+6 ∉ eighteenSevenIndices G u := by
  intro hj
  exact eighteen_no_two_seven_chords u hu h14 i
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem eighteen_nine_indices_step_three (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (i : Fin 9) (hi : i ∈ eighteenNineIndices G u) :
    i+3 ∉ eighteenNineIndices G u := by
  intro hj
  have h0 := (Finset.mem_filter.mp hi).2
  have hnext := (Finset.mem_filter.mp hj).2
  have tab : ∀ i : Fin 9,
      s(eighteenNineIndex i+3,(eighteenNineIndex i+3)+9) =
        s(eighteenNineIndex (i+3),eighteenNineIndex (i+3)+9) := by decide +kernel
  have hraw := eighteen_adj_of_edge_eq u _ _ _ _ hnext (tab i)
  exact eighteen_no_two_nine_chords u hu h14 (eighteenNineIndex i) h0 hraw

theorem eighteenSevenIndices_card_le_six (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) : (eighteenSevenIndices G u).card ≤ 6 := by
  let E := eighteenSevenIndices G u
  let f : E → Fin 6 := fun i => ⟨i.val.val % 6, Nat.mod_lt _ (by decide)⟩
  have hf : Function.Injective f := by
    intro i j he
    have hm : i.val.val % 6 = j.val.val % 6 := congrArg Fin.val he
    have tab : ∀ i j : Fin 18, i.val % 6 = j.val % 6 →
        i = j ∨ j = i+6 ∨ i = j+6 := by decide +kernel
    rcases tab i.val j.val hm with hij | hij | hij
    · exact Subtype.ext hij
    · exact False.elim (eighteen_seven_indices_step_six u hu h14 i.val i.property
        (by simpa only [← hij] using j.property))
    · exact False.elim (eighteen_seven_indices_step_six u hu h14 j.val j.property
        (by simpa only [← hij] using i.property))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem eighteenNineIndices_card_le_three (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) : (eighteenNineIndices G u).card ≤ 3 := by
  let E := eighteenNineIndices G u
  let f : E → Fin 3 := fun i => ⟨i.val.val % 3, Nat.mod_lt _ (by decide)⟩
  have hf : Function.Injective f := by
    intro i j he
    have hm : i.val.val % 3 = j.val.val % 3 := congrArg Fin.val he
    have tab : ∀ i j : Fin 9, i.val % 3 = j.val % 3 →
        i = j ∨ j = i+3 ∨ i = j+3 := by decide +kernel
    rcases tab i.val j.val hm with hij | hij | hij
    · exact Subtype.ext hij
    · exact False.elim (eighteen_nine_indices_step_three u hu h14 i.val i.property
        (by simpa only [← hij] using j.property))
    · exact False.elim (eighteen_nine_indices_step_three u hu h14 j.val j.property
        (by simpa only [← hij] using i.property))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

theorem actualEighteenChordEdges_subset (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    actualEighteenChordEdges G u ⊆
      (eighteenSevenIndices G u).image (fun i => s(u i,u (i+7))) ∪
      (eighteenNineIndices G u).image (fun i =>
        s(u (eighteenNineIndex i),u (eighteenNineIndex i+9))) := by
  intro e he
  obtain ⟨⟨i,j⟩, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ha, hn, hp⟩ := (Finset.mem_filter.mp hp).2
  rcases eighteen_noncycle_adj_positions hb h14 h16 u hu i j ha hn hp with h7 | h7 | h9
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa only [h7] using ha⟩, by rw [h7]⟩
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa only [h7] using ha.symm⟩, by rw [h7]; exact Sym2.eq_swap⟩
  · have tab : ∀ i : Fin 18, ∃ k : Fin 9,
        s(i,i+9) = s(eighteenNineIndex k,eighteenNineIndex k+9) := by decide +kernel
    obtain ⟨k,hk⟩ := tab i
    have hi : G.Adj (u i) (u (i+9)) := by simpa only [h9] using ha
    have ha' := eighteen_adj_of_edge_eq u i (i+9) _ _ hi hk.symm
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha'⟩,
      by simpa only [Sym2.map_mk, h9] using congrArg (Sym2.map u) hk.symm⟩

theorem actualEighteenChordEdges_card_le_nine (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) :
    (actualEighteenChordEdges G u).card ≤ 9 := by
  have hs := Finset.card_le_card (actualEighteenChordEdges_subset hb h14 h16 u hu)
  have hu' := Finset.card_union_le
    ((eighteenSevenIndices G u).image (fun i => s(u i,u (i+7))))
    ((eighteenNineIndices G u).image (fun i => s(u (eighteenNineIndex i),u (eighteenNineIndex i+9))))
  have he := Finset.card_image_le (s := eighteenSevenIndices G u) (f := fun i => s(u i,u (i+7)))
  have hf := Finset.card_image_le (s := eighteenNineIndices G u)
    (f := fun i => s(u (eighteenNineIndex i),u (eighteenNineIndex i+9)))
  have hcE := eighteenSevenIndices_card_le_six u hu h14
  have hcF := eighteenNineIndices_card_le_three u hu h14
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteenNineIndex
#print axioms TaskH.Seven.BP.eighteenSevenIndices
#print axioms TaskH.Seven.BP.eighteenNineIndices
#print axioms TaskH.Seven.BP.actualEighteenChordEdges
#print axioms TaskH.Seven.BP.eighteen_seven_indices_step_six
#print axioms TaskH.Seven.BP.eighteen_nine_indices_step_three
#print axioms TaskH.Seven.BP.eighteenSevenIndices_card_le_six
#print axioms TaskH.Seven.BP.eighteenNineIndices_card_le_three
#print axioms TaskH.Seven.BP.actualEighteenChordEdges_subset
#print axioms TaskH.Seven.BP.actualEighteenChordEdges_card_le_nine
