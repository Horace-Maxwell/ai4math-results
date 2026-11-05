import Research.Backfill.Paper7.MomentB6NineWeights

/-! Source-only original Z9 evaluation from complete support and actual weights.
Every ordered placement is kept.  No full labelled target is subtracted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

abbrev B6NinePair := {ij : Fin 6 × Fin 6 // ij.1 ≠ ij.2}
#print axioms Paper7MomentCounts.B6NinePair

abbrev B6NineSpike (r : ℕ) := {pair : Fin 6 × Finset (Fin 6) // pair.1 ∉ pair.2 ∧ pair.2.card = r}
#print axioms Paper7MomentCounts.B6NineSpike

abbrev B6NineTriple := {ijk : Fin 6 × (Fin 6 × Fin 6) //
  ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2}
#print axioms Paper7MomentCounts.B6NineTriple

abbrev B6NineTemplate := B6NinePair ⊕ (B6NinePair ⊕ (B6NineSpike 2 ⊕
  (B6NinePair ⊕ (B6NineTriple ⊕ (B6NineSpike 3 ⊕ B6NinePair)))))
#print axioms Paper7MomentCounts.B6NineTemplate

def b6NinePairData (M N Q : ℕ) (t : B6NinePair) : (Fin 6 → ℕ) × ℕ :=
  (b6TwoPoint M N t.val.1 t.val.2,Q)
#print axioms Paper7MomentCounts.b6NinePairData

def b6NineSpikeData (M r Q : ℕ) (t : B6NineSpike r) : (Fin 6 → ℕ) × ℕ :=
  (b6SpikeOnes M t.val.1 t.val.2,Q)
#print axioms Paper7MomentCounts.b6NineSpikeData

def b6NineTripleData (t : B6NineTriple) : (Fin 6 → ℕ) × ℕ :=
  (b6ThreePoint 6 2 1 t.val.1 t.val.2.1 t.val.2.2,8)
#print axioms Paper7MomentCounts.b6NineTripleData

def b6NineTemplateData : B6NineTemplate → (Fin 6 → ℕ) × ℕ :=
  Sum.elim (b6NinePairData 6 3 0)
    (Sum.elim (b6NinePairData 7 2 2)
      (Sum.elim (b6NineSpikeData 7 2 3)
        (Sum.elim (b6NinePairData 6 3 6)
          (Sum.elim b6NineTripleData
            (Sum.elim (b6NineSpikeData 6 3 9) (b6NinePairData 5 4 8))))))
#print axioms Paper7MomentCounts.b6NineTemplateData

def b6NineTemplateWeight : B6NineTemplate → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 3) (Sum.elim (fun _ => 4)
    (Sum.elim (fun _ => 4) (Sum.elim (fun _ => 3) (Sum.elim (fun _ => 1) (fun _ => 2))))))
#print axioms Paper7MomentCounts.b6NineTemplateWeight

theorem b6_nine_family_cards :
    Fintype.card B6NinePair = 30 ∧ Fintype.card (B6NineSpike 2) = 60 ∧
      Fintype.card (B6NineSpike 3) = 60 ∧ Fintype.card B6NineTriple = 120 := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_nine_family_cards

theorem b6_nine_pair_data_injective :
    Function.Injective (b6NinePairData 6 3 0) ∧
      Function.Injective (b6NinePairData 7 2 2) ∧
      Function.Injective (b6NinePairData 6 3 6) ∧
      Function.Injective (b6NinePairData 5 4 8) := by
  decide
#print axioms Paper7MomentCounts.b6_nine_pair_data_injective

theorem b6_nine_spike_two_data_injective : Function.Injective (b6NineSpikeData 7 2 3) := by
  decide
#print axioms Paper7MomentCounts.b6_nine_spike_two_data_injective

theorem b6_nine_spike_three_data_injective : Function.Injective (b6NineSpikeData 6 3 9) := by
  decide
#print axioms Paper7MomentCounts.b6_nine_spike_three_data_injective

theorem b6_nine_triple_data_injective : Function.Injective b6NineTripleData := by
  decide +kernel
#print axioms Paper7MomentCounts.b6_nine_triple_data_injective

theorem b6_nine_triple_ne_pair54 (t : B6NineTriple) (u : B6NinePair) :
    b6NineTripleData t ≠ b6NinePairData 5 4 8 u := by
  intro he
  have hv := congrArg (fun d : (Fin 6 → ℕ) × ℕ => d.1 t.val.1) he
  change b6ThreePoint 6 2 1 t.val.1 t.val.2.1 t.val.2.2 t.val.1 =
    b6TwoPoint 5 4 u.val.1 u.val.2 t.val.1 at hv
  have hl : b6ThreePoint 6 2 1 t.val.1 t.val.2.1 t.val.2.2 t.val.1 = 6 := by
    simp [b6ThreePoint]
  have hr : b6TwoPoint 5 4 u.val.1 u.val.2 t.val.1 ≤ 5 := by
    unfold b6TwoPoint
    split_ifs <;> omega
  omega
#print axioms Paper7MomentCounts.b6_nine_triple_ne_pair54

theorem b6NineTemplateData_injective : Function.Injective b6NineTemplateData := by
  unfold b6NineTemplateData
  apply b6_nine_pair_data_injective.1.sumElim
  · apply b6_nine_pair_data_injective.2.1.sumElim
    · apply b6_nine_spike_two_data_injective.sumElim
      · apply b6_nine_pair_data_injective.2.2.1.sumElim
        · apply b6_nine_triple_data_injective.sumElim
          · apply b6_nine_spike_three_data_injective.sumElim b6_nine_pair_data_injective.2.2.2
            intro a b he
            have hq := congrArg Prod.snd he
            norm_num [b6NineSpikeData,b6NinePairData] at hq
          · intro a b
            rcases b with b | b
            · intro he
              have hq := congrArg Prod.snd he
              norm_num [b6NineTripleData,b6NineSpikeData] at hq
            · exact b6_nine_triple_ne_pair54 a b
        · intro a b
          rcases b with b | b | b <;> intro he <;>
            have hq := congrArg Prod.snd he <;>
            norm_num [b6NinePairData,b6NineTripleData,b6NineSpikeData] at hq
      · intro a b
        rcases b with b | b | b | b <;> intro he <;>
          have hq := congrArg Prod.snd he <;>
          norm_num [b6NinePairData,b6NineTripleData,b6NineSpikeData] at hq
    · intro a b
      rcases b with b | b | b | b | b <;> intro he <;>
        have hq := congrArg Prod.snd he <;>
        norm_num [b6NinePairData,b6NineTripleData,b6NineSpikeData] at hq
  · intro a b
    rcases b with b | b | b | b | b | b <;> intro he <;>
      have hq := congrArg Prod.snd he <;>
      norm_num [b6NinePairData,b6NineTripleData,b6NineSpikeData] at hq
#print axioms Paper7MomentCounts.b6NineTemplateData_injective

theorem b6NineTemplateData_shapes (t : B6NineTemplate) :
    B6NineShapes (b6NineTemplateData t).1 (b6NineTemplateData t).2 := by
  rcases t with t | t | t | t | t | t | t
  · exact Or.inl ⟨t.val.1,t.val.2,t.property,rfl,Or.inl rfl⟩
  · exact Or.inr (Or.inl ⟨t.val.1,t.val.2,t.property,rfl,rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t.val.1,t.val.2,t.property.1,t.property.2,rfl,rfl⟩))
  · exact Or.inl ⟨t.val.1,t.val.2,t.property,rfl,Or.inr rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨t.val.1,t.val.2.1,t.val.2.2,t.property.1,t.property.2.1,t.property.2.2,rfl,rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨t.val.1,t.val.2,t.property.1,t.property.2,rfl,rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t.val.1,t.val.2,t.property,rfl,rfl⟩))))
#print axioms Paper7MomentCounts.b6NineTemplateData_shapes

theorem b6NineTemplateData_valid (t : B6NineTemplate) :
    (∑ k, (b6NineTemplateData t).1 k) = 9 ∧ (b6NineTemplateData t).2 ≤ 9 ∧
      b6ZQAccept (b6NineTemplateData t).1 (b6NineTemplateData t).2 :=
  b6_nine_shapes_accept _ _ (b6NineTemplateData_shapes t)
#print axioms Paper7MomentCounts.b6NineTemplateData_valid

def b6NineTemplateIndex (t : B6NineTemplate) : B6ZQIndex :=
  (⟨(b6NineTemplateData t).1,by have h := (b6NineTemplateData_valid t).1; omega⟩,
    ⟨(b6NineTemplateData t).2,by have h := (b6NineTemplateData_valid t).2.1; omega⟩)
#print axioms Paper7MomentCounts.b6NineTemplateIndex

theorem b6NineTemplateIndex_injective : Function.Injective b6NineTemplateIndex := by
  intro t u he
  apply b6NineTemplateData_injective
  exact congrArg (fun r : B6ZQIndex => (r.1.val,r.2.val)) he
#print axioms Paper7MomentCounts.b6NineTemplateIndex_injective

theorem b6NineTemplateIndex_tag (t : B6NineTemplate) :
    b6TotalZTag (b6NineTemplateIndex t) = (9 : Fin 37) := by
  apply Fin.ext
  exact (b6NineTemplateData_valid t).1
#print axioms Paper7MomentCounts.b6NineTemplateIndex_tag

theorem b6NineTemplateIndex_block (t : B6NineTemplate) :
    b6ZQBlock (b6NineTemplateIndex t) = b6NineTemplateWeight t := by
  classical
  change (if b6ZQAccept (b6NineTemplateData t).1 (b6NineTemplateData t).2 then
    Paper7MomentDP.boundedQDP 6 (b6NineTemplateData t).1 (b6NineTemplateData t).2 else 0) = _
  rw [ite_eq_left (b6NineTemplateData_valid t).2.2]
  rcases t with t | t | t | t | t | t | t
  · exact (b6_nine_pair63_weights t.val.1 t.val.2 t.property).1
  · exact b6_nine_pair72_weight t.val.1 t.val.2 t.property
  · exact b6_nine_spike72_weight t.val.1 t.val.2 t.property.1 t.property.2
  · exact (b6_nine_pair63_weights t.val.1 t.val.2 t.property).2
  · exact b6_nine_triple621_weight t.val.1 t.val.2.1 t.val.2.2
      t.property.1 t.property.2.1 t.property.2.2
  · exact b6_nine_spike63_weight t.val.1 t.val.2 t.property.1 t.property.2
  · exact b6_nine_pair54_weight t.val.1 t.val.2 t.property
#print axioms Paper7MomentCounts.b6NineTemplateIndex_block

def b6NineSliceWeight (r : B6ZQIndex) : ℕ :=
  if b6TotalZTag r = (9 : Fin 37) then b6ZQBlock r else 0
#print axioms Paper7MomentCounts.b6NineSliceWeight

theorem b6NineTemplateIndex_weight (t : B6NineTemplate) :
    b6NineSliceWeight (b6NineTemplateIndex t) = b6NineTemplateWeight t := by
  unfold b6NineSliceWeight
  rw [ite_eq_left (b6NineTemplateIndex_tag t)]
  exact b6NineTemplateIndex_block t
#print axioms Paper7MomentCounts.b6NineTemplateIndex_weight

theorem b6NineSliceWeight_complete_support (r : B6ZQIndex)
    (hne : b6NineSliceWeight r ≠ 0) : ∃ t, b6NineTemplateIndex t = r := by
  classical
  have htag : b6TotalZTag r = (9 : Fin 37) := by
    by_contra hn
    exact hne (ite_eq_right hn)
  have hZ : (∑ i, r.1.val i) = 9 := congrArg Fin.val htag
  have hblock : b6ZQBlock r ≠ 0 := by
    intro hz
    apply hne
    simp only [b6NineSliceWeight,ite_eq_left htag,hz]
  obtain ⟨hQ,hg,_hmax⟩ := b6_nine_nonzero_block_full_reduction r htag hblock
  have hs := b6_nine_guard_complete_shapes r.1.val r.2.val hZ hQ hg
  have from_data (t : B6NineTemplate) (hz : (b6NineTemplateData t).1 = r.1.val)
      (hq : (b6NineTemplateData t).2 = r.2.val) : ∃ u, b6NineTemplateIndex u = r := by
    refine ⟨t,?_⟩
    exact Prod.ext (Subtype.ext hz) (Fin.ext hq)
  rcases hs with ⟨i,j,hij,hz,hq⟩ | ⟨i,j,hij,hz,hq⟩ | ⟨i,s,his,hc,hz,hq⟩ |
    ⟨i,j,k,hij,hik,hjk,hz,hq⟩ | ⟨i,s,his,hc,hz,hq⟩ | ⟨i,j,hij,hz,hq⟩
  · rcases hq with hq | hq
    · exact from_data (Sum.inl ⟨(i,j),hij⟩) hz.symm hq.symm
    · exact from_data (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(i,j),hij⟩)))) hz.symm hq.symm
  · exact from_data (Sum.inr (Sum.inl ⟨(i,j),hij⟩)) hz.symm hq.symm
  · exact from_data (Sum.inr (Sum.inr (Sum.inl ⟨(i,s),his,hc⟩))) hz.symm hq.symm
  · exact from_data (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(i,(j,k)),hij,hik,hjk⟩))))) hz.symm hq.symm
  · exact from_data (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(i,s),his,hc⟩)))))) hz.symm hq.symm
  · exact from_data (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨(i,j),hij⟩)))))) hz.symm hq.symm
#print axioms Paper7MomentCounts.b6NineSliceWeight_complete_support

theorem finite_sum_eq_sum_of_injective_support {α β : Type} [Fintype α] [Fintype β]
    (f : α → ℕ) (e : β → α) (hinj : Function.Injective e)
    (hsupport : ∀ a, f a ≠ 0 → ∃ b, e b = a) : (∑ a, f a) = ∑ b, f (e b) := by
  classical
  have hsub : (Finset.univ.image e) ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
  have hz : ∀ a ∈ (Finset.univ : Finset α), a ∉ Finset.univ.image e → f a = 0 := by
    intro a _ha hn
    by_contra hf
    obtain ⟨b,hb⟩ := hsupport a hf
    exact hn (Finset.mem_image.mpr ⟨b,Finset.mem_univ b,hb⟩)
  calc
    (∑ a, f a) = ∑ a ∈ Finset.univ.image e, f a := (Finset.sum_subset hsub hz).symm
    _ = ∑ b, f (e b) := Finset.sum_image (fun a _ b _ he => hinj he)
#print axioms Paper7MomentCounts.finite_sum_eq_sum_of_injective_support

theorem b6NineTemplateWeight_sum : (∑ t, b6NineTemplateWeight t) = 960 := by
  rcases b6_nine_family_cards with ⟨hp,hs2,hs3,ht⟩
  simp [b6NineTemplateWeight,Fintype.sum_sum_type,hp,hs2,hs3,ht]
#print axioms Paper7MomentCounts.b6NineTemplateWeight_sum

theorem b6LabelledZSlice_nine_eq_nineHundredSixty : b6LabelledZSlice 9 = 960 := by
  change (∑ r, b6NineSliceWeight r) = 960
  rw [finite_sum_eq_sum_of_injective_support b6NineSliceWeight b6NineTemplateIndex
    b6NineTemplateIndex_injective b6NineSliceWeight_complete_support]
  simp only [b6NineTemplateIndex_weight]
  exact b6NineTemplateWeight_sum
#print axioms Paper7MomentCounts.b6LabelledZSlice_nine_eq_nineHundredSixty

end Paper7MomentCounts
