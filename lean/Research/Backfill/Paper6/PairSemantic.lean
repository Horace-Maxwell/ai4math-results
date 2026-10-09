import Research.Backfill.Paper6.ComplementaryPairReduction

/-! Source candidate: genuine complementary-variable blocks and the remaining
monomial family. No numerical exclusion is assumed in this semantic module. -/

set_option autoImplicit false

namespace Paper6FiveExclusion

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

def fullFamily {q : ℕ} (A B : Finset (Fin 14)) (R : Fin q → Finset (Fin 14)) :
    Fin (q + 2) → Finset (Fin 14) := Fin.cons A (Fin.cons B R)

def pairFunction {q : ℕ} (A B : Finset (Fin 14)) (R : Fin q → Finset (Fin 14)) : BFun 14 :=
  fun x => (∏ j ∈ A, x j) + (∏ j ∈ B, x j) + ∑ i, ∏ j ∈ R i, x j

theorem pairFunction_as_family {q : ℕ} (A B : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) :
    pairFunction A B R = fun x : Pt 14 => ∑ i, ∏ j ∈ fullFamily A B R i, x j := by
  funext x
  simp [pairFunction, fullFamily, Fin.sum_univ_succ, add_assoc]

def tailSelection {q : ℕ} (T : Finset (Fin (q + 2))) : Finset (Fin q) :=
  Finset.univ.filter fun i => i.succ.succ ∈ T

theorem selected_union {q : ℕ} (A B : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (T : Finset (Fin (q + 2))) :
    T.biUnion (fullFamily A B R) =
      ((if (0 : Fin (q + 2)) ∈ T then A else ∅) ∪
        (if (0 : Fin (q + 1)).succ ∈ T then B else ∅)) ∪
          (tailSelection T).biUnion R := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    have hforward (a : Fin (q + 2)) : a ∈ T → x ∈ fullFamily A B R a →
        x ∈ ((if (0 : Fin (q + 2)) ∈ T then A else ∅) ∪
          (if (0 : Fin (q + 1)).succ ∈ T then B else ∅)) ∪
            (tailSelection T).biUnion R := by
      refine Fin.cases ?_ (fun b => ?_) a
      · intro h0 hxA
        change x ∈ A at hxA
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        simpa only [ite_eq_left h0] using hxA
      · refine Fin.cases ?_ (fun c => ?_) b
        · intro h1 hxB
          change x ∈ B at hxB
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          simpa only [ite_eq_left h1] using hxB
        · intro hc hxR
          change x ∈ R c at hxR
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr
            ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩, hxR⟩
    exact hforward i hi hxi
  · intro hx
    rcases Finset.mem_union.mp hx with hxAB | hxR
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · have h0 : (0 : Fin (q + 2)) ∈ T := by
          by_contra h0
          simp [h0] at hxA
        apply Finset.mem_biUnion.mpr
        refine ⟨0, h0, ?_⟩
        change x ∈ A
        simpa only [ite_eq_left h0] using hxA
      · have h1 : (0 : Fin (q + 1)).succ ∈ T := by
          by_contra h1
          rw [Fin.succ_zero_eq_one] at h1
          simp [h1] at hxB
        apply Finset.mem_biUnion.mpr
        refine ⟨(0 : Fin (q + 1)).succ, h1, ?_⟩
        change x ∈ B
        simpa only [ite_eq_left h1] using hxB
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxR
      exact Finset.mem_biUnion.mpr ⟨i.succ.succ, (Finset.mem_filter.mp hi).2, hxi⟩

def blockCount {q : ℕ} (H : Finset (Fin 14)) (R : Fin q → Finset (Fin 14))
    (T : Finset (Fin q)) : ℕ := (H ∩ venn R T).card

def blockUnion {q : ℕ} (H : Finset (Fin 14)) (R : Fin q → Finset (Fin 14))
    (T : Finset (Fin q)) : ℕ :=
  ∑ U ∈ meetingPatterns T, blockCount H R U

theorem block_union_card {q : ℕ} (H : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (T : Finset (Fin q)) :
    (H ∩ T.biUnion R).card = blockUnion H R T := by
  rw [union_eq_venn_biUnion, Finset.inter_biUnion]
  unfold blockUnion blockCount
  apply Finset.card_biUnion
  intro U _hU V _hV hUV
  exact (venn_disjoint R hUV).mono Finset.inter_subset_right Finset.inter_subset_right

theorem block_total_le {q : ℕ} (H : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) :
    (∑ T ∈ (Finset.univ : Finset (Finset (Fin q))).filter (fun T => T.Nonempty),
      blockCount H R T) ≤ H.card := by
  have heq : meetingPatterns (Finset.univ : Finset (Fin q)) =
      (Finset.univ : Finset (Finset (Fin q))).filter (fun T => T.Nonempty) := by
    ext T
    simp [meetingPatterns]
  have h := block_union_card H R (Finset.univ : Finset (Fin q))
  rw [blockUnion, heq] at h
  rw [← h]
  exact Finset.card_le_card Finset.inter_subset_left

theorem split_card (A B V : Finset (Fin 14)) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.univ) : V.card = (A ∩ V).card + (B ∩ V).card := by
  have hv : (A ∩ V) ∪ (B ∩ V) = V := by
    ext x
    have hx : x ∈ A ∨ x ∈ B := by
      have := Finset.mem_univ x
      rw [← hu, Finset.mem_union] at this
      exact this
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  calc
    V.card = ((A ∩ V) ∪ (B ∩ V)).card := congrArg Finset.card hv.symm
    _ = (A ∩ V).card + (B ∩ V).card := Finset.card_union_of_disjoint
      (hd.mono Finset.inter_subset_left Finset.inter_subset_left)

theorem union_block_card (A B V : Finset (Fin 14)) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.univ) : (A ∪ V).card = A.card + (B ∩ V).card := by
  have heq : A ∪ V = A ∪ (B ∩ V) := by
    ext x
    have hx : x ∈ A ∨ x ∈ B := by
      have := Finset.mem_univ x
      rw [← hu, Finset.mem_union] at this
      exact this
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  rw [heq, Finset.card_union_of_disjoint (hd.mono le_rfl Finset.inter_subset_left)]

theorem block_column_card {q : ℕ} (H : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (i : Fin q) :
    (∑ T ∈ (Finset.univ : Finset (Finset (Fin q))).filter (fun T => i ∈ T),
      blockCount H R T) = (H ∩ R i).card := by
  have heq : meetingPatterns ({i} : Finset (Fin q)) =
      (Finset.univ : Finset (Finset (Fin q))).filter (fun T => i ∈ T) := by
    ext T
    simp only [meetingPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨hji, hjT⟩ := Finset.mem_inter.mp hj
      have hji' : j = i := Finset.mem_singleton.mp hji
      exact hji' ▸ hjT
    · intro hi
      exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hi⟩⟩
  have h := block_union_card H R ({i} : Finset (Fin q))
  rw [Finset.singleton_biUnion, blockUnion, heq] at h
  exact h.symm

theorem selected_card {q : ℕ} (A B : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) (T : Finset (Fin (q + 2))) :
    (T.biUnion (fullFamily A B R)).card =
      if (0 : Fin (q + 2)) ∈ T then
        if (0 : Fin (q + 1)).succ ∈ T then 14 else 7 + blockUnion B R (tailSelection T)
      else if (0 : Fin (q + 1)).succ ∈ T then 7 + blockUnion A R (tailSelection T)
      else blockUnion A R (tailSelection T) + blockUnion B R (tailSelection T) := by
  rw [selected_union]
  by_cases ha : (0 : Fin (q + 2)) ∈ T
  · by_cases hb : (0 : Fin (q + 1)).succ ∈ T
    · simp only [ha, hb, ↓reduceIte]
      rw [hu]
      calc
        ((Finset.univ : Finset (Fin 14)) ∪ (tailSelection T).biUnion R).card =
            (Finset.univ : Finset (Fin 14)).card :=
          congrArg Finset.card
            (Finset.union_eq_left.mpr (Finset.subset_univ _))
        _ = 14 := by rw [Finset.card_univ, Fintype.card_fin]
    · simp only [ha, hb, ↓reduceIte, Finset.union_empty]
      rw [union_block_card A B _ hd hu, hA, block_union_card]
  · by_cases hb : (0 : Fin (q + 1)).succ ∈ T
    · simp only [ha, hb, ↓reduceIte, Finset.empty_union]
      rw [union_block_card B A _ hd.symm (by simpa only [Finset.union_comm] using hu),
        hB, block_union_card]
    · simp only [ha, hb, ↓reduceIte, Finset.empty_union]
      rw [split_card A B _ hd hu, block_union_card, block_union_card]

def selectedCard {q : ℕ} (A B : Finset (Fin 14)) (R : Fin q → Finset (Fin 14))
    (T : Finset (Fin (q + 2))) : ℕ :=
  if (0 : Fin (q + 2)) ∈ T then
    if (0 : Fin (q + 1)).succ ∈ T then 14 else 7 + blockUnion B R (tailSelection T)
  else if (0 : Fin (q + 1)).succ ∈ T then 7 + blockUnion A R (tailSelection T)
  else blockUnion A R (tailSelection T) + blockUnion B R (tailSelection T)

theorem pair_weight_formula {q : ℕ} (A B : Finset (Fin 14))
    (R : Fin q → Finset (Fin 14)) (hA : A.card = 7) (hB : B.card = 7)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (hammingNorm (pairFunction A B R) : ℤ) =
      ∑ T ∈ (Finset.univ : Finset (Finset (Fin (q + 2)))).filter (fun T => T.Nonempty),
        (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (14 - selectedCard A B R T) := by
  rw [pairFunction_as_family, Paper6InclusionExclusion.check_Lem21]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [selected_card A B R hA hB hd hu T]
  rfl

/-- Remove exactly the two selected original indices. Repeated supports are retained. -/
theorem extract_pair {k : ℕ} (S : Fin k → Finset (Fin 14)) (hk : k ≤ 5)
    (hS : ∀ i, (S i).card ≤ 7) (i j : Fin k) (hij : i ≠ j) :
    ∃ q ≤ 3, ∃ R : Fin q → Finset (Fin 14), (∀ a, (R a).card ≤ 7) ∧
      (fun x : Pt 14 => ∑ a, ∏ b ∈ S a, x b) = pairFunction (S i) (S j) R := by
  classical
  let D : Finset (Fin k) := (Finset.univ.erase i).erase j
  let R : Fin D.card → Finset (Fin 14) := fun a => S (D.equivFin.symm a).val
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  have hc1 := Finset.card_erase_add_one (Finset.mem_univ i)
  have hc2 := Finset.card_erase_add_one hj
  have hsize : D.card + 2 = k := by
    change D.card + 1 = (Finset.univ.erase i).card at hc2
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (show D.card + 2 = (Finset.univ : Finset (Fin k)).card by omega)
  refine ⟨D.card, by omega, R, fun a => hS _, ?_⟩
  funext x
  have hrest : (∑ a ∈ D, ∏ b ∈ S a, x b) = ∑ a : Fin D.card, ∏ b ∈ R a, x b := by
    calc
      (∑ a ∈ D, ∏ b ∈ S a, x b) = ∑ a : D, ∏ b ∈ S a.val, x b :=
        (Finset.sum_coe_sort D (fun a : Fin k => ∏ b ∈ S a, x b)).symm
      _ = _ := by
        refine Fintype.sum_equiv D.equivFin
          (fun a : D => ∏ b ∈ S a.val, x b) (fun a => ∏ b ∈ R a, x b) ?_
        intro a
        dsimp only [R]
        rw [Equiv.symm_apply_apply]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
    (fun a => ∏ b ∈ S a, x b) (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (Finset.univ.erase i)
    (fun a => ∏ b ∈ S a, x b) hj]
  change (∏ b ∈ S i, x b) + ((∏ b ∈ S j, x b) + ∑ a ∈ D, ∏ b ∈ S a, x b) = _
  rw [hrest]
  exact (add_assoc _ _ _).symm

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.fullFamily
#print axioms Paper6FiveExclusion.pairFunction
#print axioms Paper6FiveExclusion.pairFunction_as_family
#print axioms Paper6FiveExclusion.tailSelection
#print axioms Paper6FiveExclusion.selected_union
#print axioms Paper6FiveExclusion.blockCount
#print axioms Paper6FiveExclusion.blockUnion
#print axioms Paper6FiveExclusion.block_union_card
#print axioms Paper6FiveExclusion.block_total_le
#print axioms Paper6FiveExclusion.split_card
#print axioms Paper6FiveExclusion.union_block_card
#print axioms Paper6FiveExclusion.block_column_card
#print axioms Paper6FiveExclusion.selected_card
#print axioms Paper6FiveExclusion.selectedCard
#print axioms Paper6FiveExclusion.pair_weight_formula
#print axioms Paper6FiveExclusion.extract_pair
