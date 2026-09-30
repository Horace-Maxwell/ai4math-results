import Research.Backfill.Paper8.Proof.Real.Lset
import Research.Backfill.Paper8.Proof.Real.Count
import Research.SwitchingThmH

/-!
# Paper 8, Proposition 5.3 (large branches)

For `b* ≥ 13`: `b* ∈ B`; the counts of Lemma 5.2 and the released `SwitchingThmH.row_budget` give
`2 N_I + N_II + 1 ≤ b* - 1`, and Lemma 4.1 gives `|ℒ_{b*}| = k_{b*} b* - 1 ≥ b* - 1`, which is
(a′) at `β = b*`; the good member of the leaf row is Corollary 4.4.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Real

theorem bstar_mem {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k) :
    bstar (branchMS a) ∈ Bset (branchMS a) := by
  have hne : (Bset (branchMS a)).Nonempty := ⟨a ⟨0, hk⟩, by simp [Bset, branchMS]⟩
  obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup (Bset (branchMS a)) hne id
  unfold bstar
  rw [hbeq]
  exact hb

theorem gapCount_le (m : Multiset ℕ) : gapCount m ≤ bstar m + 1 := by
  unfold gapCount
  exact (Finset.card_le_card Finset.sdiff_subset).trans (by simp)

/-- **Proposition 5.3**, from Lemmas 3.1(i), 3.3(b), 3.3(d) (through Lemma 5.2) and Corollary 4.4. -/
theorem prop_5_3 (h31 : Lemma_3_1_i) (h33b : Lemma_3_3_b) (h33d : Lemma_3_3_d)
    (h44 : Cor_4_4) : Prop_5_3 := by
  intro k a hk hbs
  have hmem := bstar_mem a hk
  have hkb : 1 ≤ kb (branchMS a) (bstar (branchMS a)) := by
    unfold kb
    exact Multiset.one_le_count_iff_mem.2 (Multiset.mem_toFinset.1 hmem)
  have hL := ((lemma_4_1 (bstar (branchMS a)) (kb (branchMS a) (bstar (branchMS a)))
    (by omega) hkb).1 (by omega)).2
  have hex : ¬ (bstar (branchMS a) = 2 ∧ kb (branchMS a) (bstar (branchMS a)) = 2) := by omega
  simp only [hex, ite_false, Nat.sub_zero] at hL
  have H := lemma_5_2 h31 h33b h33d k a hk (by omega)
  dsimp only at H
  obtain ⟨hr, hsq, hsqg, hNI, htot⟩ := H
  have hg := gapCount_le (branchMS a)
  have hbud := SwitchingThmH.row_budget (bstar (branchMS a))
    (sqCountB (Bset (branchMS a)) (bstar (branchMS a))) (gapCount (branchMS a))
    (NI (branchMS a)) (NII (branchMS a)) hbs hsq hsqg hNI (by omega)
  have hcrit : CritAat (branchMS a) (bstar (branchMS a)) := by
    unfold CritAat
    rw [hL]
    have := Nat.le_mul_of_pos_left (bstar (branchMS a)) (show 0 < kb (branchMS a)
      (bstar (branchMS a)) by omega)
    omega
  refine ⟨hmem, hcrit, fun mem hmem' => ?_⟩
  exact (h44 k a hk (by omega)).1 _ hmem (by omega) hcrit mem hmem'

end P8Real
