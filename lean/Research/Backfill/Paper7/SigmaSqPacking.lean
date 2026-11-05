import Research.Backfill.Paper7.ChallengeV2

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
The square-sum packing bound is proved from actual multiplicities: a sorted
prefix with maximum m has at most four copies of each integer in [2,m].
No packing conclusion or spectral formula is assumed, and no compilation or
kernel acceptance of this candidate is claimed. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Paper7Rank
open BackfillPaper7.Challenge

/-- At most four copies of each integer in the genuine support interval [2,m]. -/
theorem sigmaSq_bounded_card (s : Multiset ℕ) (m : ℕ)
    (hmin : ∀ a ∈ s, 2 ≤ a) (hmax : ∀ a ∈ s, a ≤ m)
    (hcount : ∀ a, s.count a ≤ 4) : s.card ≤ 4 * (m - 1) := by
  have hle : s ≤ 4 • (Finset.Icc 2 m).val := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ s
    · have hai : a ∈ (Finset.Icc 2 m).val :=
        Finset.mem_Icc.mpr ⟨hmin a ha, hmax a ha⟩
      have hc : (Finset.Icc 2 m).val.count a = 1 :=
        Multiset.count_eq_one_of_mem (Finset.Icc 2 m).nodup hai
      rw [Multiset.count_nsmul, hc, mul_one]
      exact hcount a
    · rw [Multiset.count_eq_zero_of_notMem ha]
      exact Nat.zero_le _
  have hc := Multiset.card_le_card hle
  rw [Multiset.card_nsmul] at hc
  change s.card ≤ 4 * (Finset.Icc 2 m).card at hc
  rw [Nat.card_Icc] at hc
  omega
#print axioms Paper7Rank.sigmaSq_bounded_card

/-- The i-th value in a sorted list cannot be below i/4+2. -/
theorem sigmaSq_sorted_get_bound (l : List ℕ) (hsort : l.Pairwise (· ≤ ·))
    (hmin : ∀ a ∈ l, 2 ≤ a) (hcount : ∀ a, l.count a ≤ 4)
    (i : Fin l.length) : i.val / 4 + 2 ≤ l.get i := by
  let t : Multiset ℕ := (l.take (i.val + 1) : List ℕ)
  have htle : t ≤ (l : Multiset ℕ) :=
    Multiset.coe_le.mpr (List.take_sublist (i.val + 1) l).subperm
  have htmin : ∀ a ∈ t, 2 ≤ a := by
    intro a ha
    exact hmin a (Multiset.mem_coe.mp (Multiset.mem_of_le htle ha))
  have htmax : ∀ a ∈ t, a ≤ l.get i := by
    intro a ha
    have hmem : a ∈ l.take (i.val + 1) := Multiset.mem_coe.mp ha
    rcases List.mem_take_iff_getElem.mp hmem with ⟨j, hj, hja⟩
    have hjl : j < l.length := by omega
    have heq : l.get ⟨j, hjl⟩ = a := hja
    rw [← heq]
    apply hsort.rel_get_of_le
    change j ≤ i.val
    omega
  have htcount : ∀ a, t.count a ≤ 4 := by
    intro a
    exact (Multiset.count_le_of_le a htle).trans
      (by simpa only [Multiset.coe_count] using hcount a)
  have hc := sigmaSq_bounded_card t (l.get i) htmin htmax htcount
  have hlen : t.card = i.val + 1 := by
    change (l.take (i.val + 1)).length = i.val + 1
    exact List.length_take_of_le (by omega)
  rw [hlen] at hc
  have htwo : 2 ≤ l.get i := hmin _ (List.get_mem l i)
  omega
#print axioms Paper7Rank.sigmaSq_sorted_get_bound

/-- The frozen sigmaSq is the minimum square sum allowed by these multiplicity bounds. -/
theorem sigmaSq_packing (s : Multiset ℕ)
    (hmin : ∀ a ∈ s, 2 ≤ a) (hcount : ∀ a, s.count a ≤ 4) :
    sigmaSq (s.card : ℤ) ≤ (s.map (fun a => a ^ 2)).sum := by
  let l : List ℕ := s.sort (· ≤ ·)
  have hl : (l : Multiset ℕ) = s := Multiset.sort_eq s (· ≤ ·)
  have hlen : l.length = s.card := by
    simpa only [Multiset.coe_card] using congrArg Multiset.card hl
  have hsort : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort s (· ≤ ·)
  have hminl : ∀ a ∈ l, 2 ≤ a := by
    intro a ha
    apply hmin a
    rw [← hl]
    exact ha
  have hcountl : ∀ a, l.count a ≤ 4 := by
    intro a
    simpa only [← hl, Multiset.coe_count] using hcount a
  have hcomp : (∑ i : Fin l.length, (i.val / 4 + 2) ^ 2) ≤
      ∑ i : Fin l.length, (l.get i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := sigmaSq_sorted_get_bound l hsort hminl hcountl i
    simpa only [pow_two] using Nat.mul_le_mul hi hi
  have hleft : sigmaSq (s.card : ℤ) =
      ∑ i : Fin l.length, (i.val / 4 + 2) ^ 2 := by
    calc
      sigmaSq (s.card : ℤ) =
          ∑ j ∈ Finset.range l.length, (j / 4 + 2) ^ 2 := by
            simp only [sigmaSq, Int.toNat_natCast, hlen]
      _ = _ := (Fin.sum_univ_eq_sum_range (fun j : ℕ => (j / 4 + 2) ^ 2) l.length).symm
  have hright : (∑ i : Fin l.length, (l.get i) ^ 2) =
      (s.map (fun a => a ^ 2)).sum := by
    have hmap : List.ofFn (fun i : Fin l.length => (l.get i) ^ 2) =
        l.map (fun a => a ^ 2) := by
      simpa only [List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map l (fun a : ℕ => a ^ 2))
    rw [← Fin.sum_ofFn, hmap, ← hl, Multiset.map_coe, Multiset.sum_coe]
  exact hleft.trans_le (hcomp.trans_eq hright)
#print axioms Paper7Rank.sigmaSq_packing

end Paper7Rank
