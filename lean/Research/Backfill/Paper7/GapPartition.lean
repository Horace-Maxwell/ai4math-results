import Research.Backfill.Paper7.Lemma22GapBounds

/-! The actual partition of the unsupported vertices by frozen cyclic gaps.
Coverage is proved by a least rotation distance, and uniqueness by cancellation
of permutation powers. This source candidate has not been compiled. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge

theorem rotate_pow_add_apply (b : ℕ) (k : Fin b) (m n : ℕ) :
    ((finRotate b) ^ (m + n)) k =
      ((finRotate b) ^ m) (((finRotate b) ^ n) k) := by
  rw [pow_add, Equiv.Perm.mul_apply]
#print axioms Paper7Lemma22Gaps.rotate_pow_add_apply

theorem rotate_pow_card_apply (b : ℕ) (k : Fin b) :
    ((finRotate b) ^ b) k = k := by
  let : NeZero b := k.neZero
  rw [rotate_pow_apply, Fin.natCast_self, add_zero]
#print axioms Paper7Lemma22Gaps.rotate_pow_card_apply

/-- Every vertex is reached in fewer than b steps, including zero steps. -/
theorem rotate_reaches_lt (b : ℕ) (k j : Fin b) :
    ∃ n : ℕ, n < b ∧ ((finRotate b) ^ n) k = j := by
  let : NeZero b := k.neZero
  refine ⟨(j - k).val, (j - k).isLt, ?_⟩
  rw [rotate_pow_apply, Fin.cast_val_eq_self]
  exact add_sub_cancel k j
#print axioms Paper7Lemma22Gaps.rotate_reaches_lt

theorem inGap_not_mem (b : ℕ) (K : Finset (Fin b)) (k j : Fin b)
    (hgap : inGap b K k j) : j ∉ K := by
  obtain ⟨d, hd, hend, hclear⟩ := hgap
  have hnot := hclear d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, le_rfl⟩)
  simpa only [hend] using hnot
#print axioms Paper7Lemma22Gaps.inGap_not_mem

/-- A clear segment from a supported start cannot make a full turn. -/
theorem gap_witness_lt_card (b : ℕ) (K : Finset (Fin b)) (k : Fin b)
    (hk : k ∈ K) (d : ℕ) (hd : d ∈ Finset.Icc 1 b)
    (hclear : ∀ t ∈ Finset.Icc 1 d, ((finRotate b) ^ t) k ∉ K) : d < b := by
  by_contra hnot
  have hbounds := Finset.mem_Icc.mp hd
  have he : d = b := by omega
  have hbad := hclear d (Finset.mem_Icc.mpr ⟨hbounds.1, le_rfl⟩)
  rw [he, rotate_pow_card_apply] at hbad
  exact hbad hk
#print axioms Paper7Lemma22Gaps.gap_witness_lt_card

/-- Two supported starts of a clear segment ending at the same vertex coincide. -/
theorem inGap_unique_start (b : ℕ) (K : Finset (Fin b)) (k l j : Fin b)
    (hk : k ∈ K) (hl : l ∈ K)
    (hjk : inGap b K k j) (hjl : inGap b K l j) : k = l := by
  obtain ⟨d, _, hdk, hclear_k⟩ := hjk
  obtain ⟨e, _, hel, hclear_l⟩ := hjl
  rcases lt_trichotomy d e with hlt | heq | hgt
  · have hstep : ((finRotate b) ^ (e - d)) l = k := by
      apply ((finRotate b) ^ d).injective
      rw [← rotate_pow_add_apply b l d (e - d), show d + (e - d) = e by omega]
      exact hel.trans hdk.symm
    have hbad := hclear_l (e - d) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hstep] at hbad
    exact False.elim (hbad hk)
  · subst e
    exact ((finRotate b) ^ d).injective (hdk.trans hel.symm)
  · have hstep : ((finRotate b) ^ (d - e)) k = l := by
      apply ((finRotate b) ^ e).injective
      rw [← rotate_pow_add_apply b k e (d - e), show e + (d - e) = d by omega]
      exact hdk.trans hel.symm
    have hbad := hclear_k (d - e) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hstep] at hbad
    exact False.elim (hbad hl)
#print axioms Paper7Lemma22Gaps.inGap_unique_start

/-- Actual coverage: a nearest supported start has no supported interior point. -/
theorem exists_gap_start (b : ℕ) (K : Finset (Fin b)) (hK : K.Nonempty)
    (j : Fin b) (hj : j ∉ K) : ∃ k, k ∈ K ∧ inGap b K k j := by
  classical
  let P : ℕ → Prop := fun n => ∃ k, k ∈ K ∧ ((finRotate b) ^ n) k = j
  obtain ⟨k0, hk0⟩ := hK
  obtain ⟨n0, hn0, hreach⟩ := rotate_reaches_lt b k0 j
  have hex : ∃ n, P n := ⟨n0, k0, hk0, hreach⟩
  let d := Nat.find hex
  obtain ⟨k, hk, hend⟩ := Nat.find_spec hex
  change ((finRotate b) ^ d) k = j at hend
  have hdle : d ≤ n0 := Nat.find_min' hex ⟨k0, hk0, hreach⟩
  have hdlt : d < b := lt_of_le_of_lt hdle hn0
  have hdpos : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := by omega
    have he : k = j := by simpa only [hd0, pow_zero, Equiv.Perm.one_apply] using hend
    exact hj (he ▸ hk)
  refine ⟨k, hk, d, Finset.mem_Icc.mpr ⟨hdpos, hdlt.le⟩, hend, ?_⟩
  intro t ht htK
  have htbounds := Finset.mem_Icc.mp ht
  have hsmaller : d - t < d := by omega
  have hP : P (d - t) := by
    refine ⟨((finRotate b) ^ t) k, htK, ?_⟩
    rw [← rotate_pow_add_apply b k (d - t) t, show d - t + t = d by omega]
    exact hend
  exact Nat.find_min hex hsmaller hP
#print axioms Paper7Lemma22Gaps.exists_gap_start

theorem existsUnique_gap_start (b : ℕ) (K : Finset (Fin b)) (hK : K.Nonempty)
    (j : Fin b) (hj : j ∉ K) : ∃! k, k ∈ K ∧ inGap b K k j := by
  obtain ⟨k, hk, hgap⟩ := exists_gap_start b K hK j hj
  refine ⟨k, ⟨hk, hgap⟩, ?_⟩
  intro l hl
  exact inGap_unique_start b K l k j hl.1 hk hl.2 hgap
#print axioms Paper7Lemma22Gaps.existsUnique_gap_start

/-- An unsupported predecessor of an interior vertex stays in the same gap. -/
theorem inGap_prev (b : ℕ) (K : Finset (Fin b)) (k j : Fin b)
    (hk : k ∈ K) (hgap : inGap b K k j) (hprev : prv b j ∉ K) :
    inGap b K k (prv b j) := by
  obtain ⟨d, hd, hend, hclear⟩ := hgap
  have hbounds := Finset.mem_Icc.mp hd
  have hd2 : 2 ≤ d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    have hnxt : nxt b k = j := by simpa only [hd1, pow_one, nxt] using hend
    apply hprev
    rw [← hnxt]
    change (finRotate b).symm ((finRotate b) k) ∈ K
    simpa only [Equiv.symm_apply_apply] using hk
  refine ⟨d - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · have hpred := prv_rotate_pow_succ b k (d - 1)
    rw [show d - 1 + 1 = d by omega, hend] at hpred
    exact hpred.symm
  · intro t ht
    have htbounds := Finset.mem_Icc.mp ht
    exact hclear t (Finset.mem_Icc.mpr ⟨htbounds.1, by omega⟩)
#print axioms Paper7Lemma22Gaps.inGap_prev

/-- An unsupported successor of an interior vertex stays in the same gap. -/
theorem inGap_next (b : ℕ) (K : Finset (Fin b)) (k j : Fin b)
    (hk : k ∈ K) (hgap : inGap b K k j) (hnext : nxt b j ∉ K) :
    inGap b K k (nxt b j) := by
  obtain ⟨d, hd, hend, hclear⟩ := hgap
  have hdlt := gap_witness_lt_card b K k hk d hd hclear
  refine ⟨d + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · exact (nxt_rotate_pow b k d).symm.trans (congrArg (nxt b) hend)
  · intro t ht
    have htbounds := Finset.mem_Icc.mp ht
    by_cases htd : t ≤ d
    · exact hclear t (Finset.mem_Icc.mpr ⟨htbounds.1, htd⟩)
    · have he : t = d + 1 := by omega
      subst t
      rw [← nxt_rotate_pow, hend]
      exact hnext
#print axioms Paper7Lemma22Gaps.inGap_next

end Paper7Lemma22Gaps
