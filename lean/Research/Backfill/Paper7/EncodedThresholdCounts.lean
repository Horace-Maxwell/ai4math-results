import Research.Backfill.Paper7.ActualSpectralCounts
import Research.Backfill.Paper7.BoundedSpectralSums

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported actual-count and bounded-spectrum modules are pending candidates.
Both signs of an odd graph are counted separately; no spectral symmetry is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy Paper7PruningSpectrum
open scoped BigOperators

theorem positive_filtered_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (p : ℝ → Prop) [DecidablePred p] :
    ((Bplus G).filter p).card =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => p (value i)), mult G (value i) := by
  classical
  calc
    ((Bplus G).filter p).card =
        ∑ i : Fin 8, ((Bplus G).filter p).count (value i : ℝ) :=
      finite_count_card ((Bplus G).filter p) (fun i : Fin 8 => (value i : ℝ))
        value_real_injective (fun a ha => positive_support G hG hwin a
          (Multiset.mem_of_mem_filter ha))
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have hc : (Bplus G).count (value i : ℝ) = mult G (value i) :=
        Multiset.count_filter_of_pos (value_lower_bound i)
      rw [Multiset.count_filter, hc]
#print axioms Paper7PruningGuards.positive_filtered_card

theorem negative_filtered_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (p : ℝ → Prop) [DecidablePred p] :
    (((spec G).filter (fun x => x ≤ -2)).filter p).card =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => p (-(value i : ℝ))),
        mult G (-(value i : ℝ)) := by
  classical
  calc
    (((spec G).filter (fun x => x ≤ -2)).filter p).card =
        ∑ i : Fin 8, (((spec G).filter (fun x => x ≤ -2)).filter p).count
          (-(value i : ℝ)) :=
      finite_count_card (((spec G).filter (fun x => x ≤ -2)).filter p)
        (fun i : Fin 8 => -(value i : ℝ)) neg_value_real_injective
        (fun a ha => negative_support G hG hwin a (Multiset.mem_of_mem_filter ha))
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have hv := value_lower_bound i
      have hc : ((spec G).filter (fun x => x ≤ -2)).count (-(value i : ℝ)) =
          mult G (-(value i : ℝ)) :=
        Multiset.count_filter_of_pos (by linarith : -(value i : ℝ) ≤ -2)
      rw [Multiset.count_filter, hc]
#print axioms Paper7PruningGuards.negative_filtered_card

theorem Ngt_expansion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (m : ℕ) (hm : 1 ≤ m) :
    Ngt G m = ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => m < value i),
      mult G (value i) := by
  classical
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (Bplus G).filter (fun a => (m : ℝ) < a) =
      (spec G).filter (fun a => (m : ℝ) < a) := by
    rw [positive_filter_eq_threshold G hG, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro a _
    exact ⟨And.left, fun h => ⟨h, hmR.trans_lt h⟩⟩
  have h := positive_filtered_card G hG hwin (fun a => (m : ℝ) < a)
  rw [hf] at h
  simpa only [Ngt, Nat.cast_lt] using h
#print axioms Paper7PruningGuards.Ngt_expansion

theorem Nlt_expansion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (m : ℕ) (hm : 1 ≤ m) :
    Nlt G (-(m : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => m < value i),
        mult G (-(value i : ℝ)) := by
  classical
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : ((spec G).filter (fun a => a ≤ -2)).filter (fun a => a < -(m : ℝ)) =
      (spec G).filter (fun a => a < -(m : ℝ)) := by
    rw [negative_filter_eq_threshold G hG, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro a _
    exact ⟨And.left, fun h => ⟨h, by linarith⟩⟩
  have h := negative_filtered_card G hG hwin (fun a => a < -(m : ℝ))
  rw [hf] at h
  simpa only [Nlt, neg_lt_neg_iff, Nat.cast_lt] using h
#print axioms Paper7PruningGuards.Nlt_expansion

theorem Nge_expansion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (m : ℕ) (hm : 2 ≤ m) :
    Nge G m = ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => m ≤ value i),
      mult G (value i) := by
  classical
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (Bplus G).filter (fun a => (m : ℝ) ≤ a) =
      (spec G).filter (fun a => (m : ℝ) ≤ a) := by
    rw [Bplus, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro a _
    exact ⟨And.left, fun h => ⟨h, hmR.trans h⟩⟩
  have h := positive_filtered_card G hG hwin (fun a => (m : ℝ) ≤ a)
  rw [hf] at h
  simpa only [Nge, Nat.cast_le] using h
#print axioms Paper7PruningGuards.Nge_expansion

theorem Nle_expansion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (m : ℕ) (hm : 2 ≤ m) :
    Nle G (-(m : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 8 => m ≤ value i),
        mult G (-(value i : ℝ)) := by
  classical
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : ((spec G).filter (fun a => a ≤ -2)).filter (fun a => a ≤ -(m : ℝ)) =
      (spec G).filter (fun a => a ≤ -(m : ℝ)) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro a _
    exact ⟨And.left, fun h => ⟨h, by linarith⟩⟩
  have h := negative_filtered_card G hG hwin (fun a => a ≤ -(m : ℝ))
  rw [hf] at h
  simpa only [Nle, neg_le_neg_iff, Nat.cast_le] using h
#print axioms Paper7PruningGuards.Nle_expansion

theorem actualCounts_specGT (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2))
    (m : ℕ) (hm : 1 ≤ m) :
    specGT b (actualCounts b x hb) m =
      if Even b then Ngt (SG b x.1 x.2) m
      else min (Ngt (SG b x.1 x.2) m) (Nlt (SG b x.1 x.2) (-(m : ℝ))) := by
  have hw := budget_spectral_window b N x hb hN hx
  have hp := Ngt_expansion (SG b x.1 x.2) hG hw m hm
  have hn := Nlt_expansion (SG b x.1 x.2) hG hw m hm
  by_cases he : Even b
  · simp only [specGT, ite_eq_left he, actualCounts_pos]
    exact hp.symm
  · have ho := Nat.not_even_iff_odd.mp he
    simp only [specGT, ite_eq_right he, actualCounts_pos, actualCounts_neg_odd b x hb ho]
    rw [hp, hn]
#print axioms Paper7PruningGuards.actualCounts_specGT

theorem actualCounts_specGE (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2))
    (m : ℕ) (hm : 2 ≤ m) :
    specGE b (actualCounts b x hb) m =
      if Even b then Nge (SG b x.1 x.2) m
      else min (Nge (SG b x.1 x.2) m) (Nle (SG b x.1 x.2) (-(m : ℝ))) := by
  have hw := budget_spectral_window b N x hb hN hx
  have hp := Nge_expansion (SG b x.1 x.2) hG hw m hm
  have hn := Nle_expansion (SG b x.1 x.2) hG hw m hm
  have hm0 : ¬ m < 2 := by omega
  by_cases he : Even b
  · simp only [specGE, ite_eq_right hm0, ite_eq_left he, actualCounts_pos]
    exact hp.symm
  · have ho := Nat.not_even_iff_odd.mp he
    simp only [specGE, ite_eq_right hm0, ite_eq_right he,
      actualCounts_pos, actualCounts_neg_odd b x hb ho]
    rw [hp, hn]
#print axioms Paper7PruningGuards.actualCounts_specGE

end Paper7PruningGuards
