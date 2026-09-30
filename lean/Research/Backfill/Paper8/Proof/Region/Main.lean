import Research.Backfill.Paper8.Proof.Region.Crit
import Research.Backfill.Paper8.Proof.Region.Search
import Research.Backfill.Paper8.Proof.Spec.Main
import Research.Backfill.Paper8.Proof.Real.Main
import Research.Backfill.Paper8.Proof.Orb.Main

/-!
# Paper 8: Lemma 5.4 and Proposition 5.5 (agent `region`)

Final statements, of the exact types of the frozen statements, without hypotheses. Lemma 5.4:
the implication by the paper's argument from Lemma 5.2 (agent `real`, with Lemmas 3.1(i), 3.3(b)
and 3.3(d) of agents `spec` and `orb`); the finite part from `regionR = msOf '' enum`
(`Research.Backfill.Paper8.Proof.Region.Bridge`, with Lemma 4.1) and the kernel evaluation of `enum` (`Research.Backfill.Paper8.Proof.Region.Search`).
Proposition 5.5: every tree of `enum` passes `checkTree`, which accepts a tree if it passes the
test `critT` or is one of the three exceptions of the statement (`isExc`); `critT` is sound
(`Research.Backfill.Paper8.Proof.Region.Crit`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Region

theorem check_Lemma_5_4 : BackfillPaper8.Challenge.Lemma_5_4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k a hk h2 h12 hA hB
    obtain ⟨-, -, -, hNI, hd⟩ := P8Real.check_Lemma_5_2 P8Spec.check_Lemma_3_1_i
      P8Orb.check_Lemma_3_3_b P8Orb.check_Lemma_3_3_d k a hk (by omega)
    refine ⟨h2, h12, ?_, ?_⟩
    · intro β hβ hβ1
      have hL : ¬ CritAat (branchMS a) β := fun h => hA ⟨β, hβ, hβ1, h⟩
      unfold CritAat at hL
      unfold MB nuB
      omega
    · intro hk0
      have hB' : ¬ (4 * NI (branchMS a) + 2 * NII (branchMS a) + Nei (branchMS a) <
          2 * (kb (branchMS a) 0 + 1)) := fun h => hB ⟨hk0, h⟩
      unfold nuB
      omega
  · rw [regionR_eq]
    exact (List.finite_toSet enum).image _
  · rw [regionR_eq, msOf_injOn.ncard_image]
    have h : {T | T ∈ enum} = (enum.toFinset : Set (List (ℕ × ℕ))) := by
      ext T
      simp
    rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup_enum, length_enum]
  · intro m hm
    rw [regionR_eq] at hm
    obtain ⟨T, hT, rfl⟩ := hm
    have hc := checkTree_of_mem_enum hT
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hn := hc.1.1
    unfold nOf at hn
    rw [card_msOf, sum_msOf]
    omega

#print axioms check_Lemma_5_4

theorem check_Prop_5_5 : BackfillPaper8.Challenge.Prop_5_5 := by
  intro m hm h1 h2 h3
  rw [regionR_eq] at hm
  obtain ⟨T, hT, rfl⟩ := hm
  have hc := checkTree_of_mem_enum hT
  simp only [checkTree, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨-, h48⟩, hc | hx⟩ := hc
  · exact crit_of_critT hT h48 hc
  · exfalso
    simp only [isExc, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1 (by decide)
    · exact h2 (by decide)
    · exact h3 (by decide)

#print axioms check_Prop_5_5

end P8Region
