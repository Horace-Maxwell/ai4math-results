import Research.Backfill.Paper7.LegacyEnumeration
import Research.Backfill.Paper7.GapPartition
import Research.Backfill.Paper7.RankCardinality
import Research.Backfill.Paper7.SigmaSqBounds

/-!
Source-only author candidate by Codex subagent p6_binding_spotcheck.
The literal C(rank=true) guard at b=13, N=41 is impossible already from
Budget and PatternPass. No integral-spectrum hypothesis is imposed on the
candidate graph. The strict odd-cycle gap bound below is proved directly from
the frozen gap witnesses by induction on a rotation return time.
This new source has not been compiled or accepted by either kernel.
-/

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace Paper7PruningEmpty
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

/-- If every first supported hit has even distance, then every supported
return distance is even, including distances longer than one full turn. -/
theorem even_gap_hit_time_even (b : ℕ) (K : Finset (Fin b))
    (hAll : ∀ k ∈ K, ∃ d ∈ Finset.Icc 1 b, Even d ∧
      ((finRotate b) ^ d) k ∈ K ∧
      ∀ t ∈ Finset.Ico 1 d, ((finRotate b) ^ t) k ∉ K) :
    ∀ n : ℕ, ∀ k : Fin b, k ∈ K → ((finRotate b) ^ n) k ∈ K → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk hhit
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, rfl⟩
    obtain ⟨d, hd, hdeven, hnext, hclear⟩ := hAll k hk
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdle : d ≤ n := by
      by_contra h
      exact (hclear n (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)) hhit
    have hrest : ((finRotate b) ^ (n - d)) (((finRotate b) ^ d) k) ∈ K := by
      rw [← Paper7Lemma22Gaps.rotate_pow_add_apply b k (n - d) d,
        Nat.sub_add_cancel hdle]
      exact hhit
    have heven := ih (n - d) (by omega) (((finRotate b) ^ d) k) hnext hrest
    obtain ⟨a, ha⟩ := heven
    obtain ⟨c, hc⟩ := hdeven
    exact ⟨a + c, by omega⟩
#print axioms Paper7PruningEmpty.even_gap_hit_time_even

/-- A nonempty support on an odd cycle has at least one odd-length gap. -/
theorem evenGaps_lt_card_of_odd (b : ℕ) (K : Finset (Fin b))
    (ho : Odd b) (hK : K.Nonempty) : evenGaps b K < K.card := by
  classical
  let P : Fin b → Prop := fun k => ∃ d ∈ Finset.Icc 1 b, Even d ∧
    ((finRotate b) ^ d) k ∈ K ∧
    ∀ t ∈ Finset.Ico 1 d, ((finRotate b) ^ t) k ∉ K
  have hle : evenGaps b K ≤ K.card := Finset.card_filter_le K P
  by_contra hnot
  have hcard : (K.filter P).card = K.card := by
    change evenGaps b K = K.card
    omega
  have hAll : ∀ k ∈ K, P k := Finset.card_filter_eq_iff.mp hcard
  obtain ⟨k, hk⟩ := hK
  have hreturn : ((finRotate b) ^ b) k ∈ K := by
    rw [Paper7Lemma22Gaps.rotate_pow_card_apply]
    exact hk
  have heven := even_gap_hit_time_even b K hAll b k hk hreturn
  exact (Nat.not_even_iff_odd.mpr ho) heven
#print axioms Paper7PruningEmpty.evenGaps_lt_card_of_odd

theorem delta0_lt_card_of_odd_nonempty (b : ℕ) (p : Fin b → ℕ)
    (ho : Odd b) (hK : (Kp b p).Nonempty) : delta0 b p < (Kp b p).card := by
  rw [delta0, ite_eq_right hK.ne_empty]
  exact evenGaps_lt_card_of_odd b (Kp b p) ho hK
#print axioms Paper7PruningEmpty.delta0_lt_card_of_odd_nonempty

/-- Only the original positive-weight budget and rank=true, refined=false
pattern guard are used; canonicality and spectral integrality are unnecessary. -/
theorem pattern_c_thirteen_false (x : PQ 13) (hbudget : Budget 13 41 x)
    (hpattern : PatternPass true false 13 41 x) : False := by
  classical
  have hguard := hpattern.1 rfl
  change (sigmaSq ((13 : ℤ) + (Kp 13 x.1).card - delta0 13 x.1 -
    (if (Kq 13 x.2).card = 0 then 4 else 0)) : ℤ) ≤ 82 at hguard
  have harg : (10 : ℤ) ≤ 13 + (Kp 13 x.1).card - delta0 13 x.1 -
      (if (Kq 13 x.2).card = 0 then 4 else 0) := by
    by_cases hq : (Kq 13 x.2).card = 0
    · have hqempty : Kq 13 x.2 = ∅ := Finset.card_eq_zero.mp hq
      have hqzero : qSum x = 0 := Paper7Rank.support_sum_zero 13 x.2 hqempty
      have hpnonempty : (Kp 13 x.1).Nonempty := by
        by_contra hp
        have hpempty : Kp 13 x.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
        have hpzero : pSum x = 0 := Paper7Rank.support_sum_zero 13 x.1 hpempty
        have hpos := hbudget.1
        rw [weight, hpzero, hqzero] at hpos
        omega
      have hd := delta0_lt_card_of_odd_nonempty 13 x.1 (by decide) hpnonempty
      rw [ite_eq_left hq]
      omega
    · have hd := Paper7Rank.delta0_le_card_add_two 13 x.1
      rw [ite_eq_right hq, sub_zero]
      omega
  have hs := Paper7Rank.sigmaSq_monotone harg
  rw [Paper7Rank.sigmaSq_ten] at hs
  have hsZ : (84 : ℤ) ≤ sigmaSq ((13 : ℤ) + (Kp 13 x.1).card - delta0 13 x.1 -
      (if (Kq 13 x.2).card = 0 then 4 else 0)) := by exact_mod_cast hs
  omega
#print axioms Paper7PruningEmpty.pattern_c_thirteen_false

theorem pruning_c_thirteen_empty : LeafSet (.c true) 13 41 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact pattern_c_thirteen_false x hx.2.1 hx.2.2.1
#print axioms Paper7PruningEmpty.pruning_c_thirteen_empty

end Paper7PruningEmpty
