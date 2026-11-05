import Research.Backfill.Paper7.PQPrefixCompletion

/-! Source-only candidate for the exact D table completion interpretation.
No positivity of pendant weight is imposed: the right side includes bare cycles.
Both d=0 and d=b use the same explicit prefix/suffix construction. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem dReachable_completion_iff (load cyc : Bool) (b N d : ℕ)
    (he : Even b) (hbN : b ≤ N) (hN : N ≤ 49) (hd : d ≤ b)
    (x : PQ b) (hweight : weight («prefix» d x) ≤ N-b) :
    (DReachable load cyc b N (b-d) (weight («prefix» d x))
      (qSum («prefix» d x)) (prefixTheta d x).toNat ↔
      ∃ y : PQ b, b + weight y ≤ N ∧ «prefix» d y = «prefix» d x ∧
        MomentPass cyc load false b N y) := by
  classical
  have htcast : ((prefixTheta d x).toNat : ℤ) = prefixTheta d x :=
    Int.toNat_of_nonneg (prefixTheta_nonneg d x)
  have htlt : (prefixTheta d x).toNat < 3072 := by
    have h := prefixTheta_lt_storage_bound b N d hd x hbN hweight hN
    omega
  constructor
  · rintro ⟨_ht, s, hs, _he, wr, Qr, tr, hw, _hQ, hreach, htarget, hs2, hload⟩
    obtain ⟨z, hzw, hzt, hzQ⟩ : ∃ z : PQ (b-d), weight z = wr ∧ theta z = tr ∧
        (load = true → qSum z = Qr) := by
      cases load with
      | false =>
        obtain ⟨z, hzw, hzt⟩ :=
          (reachD1_iff (b-d) wr tr (reachD1_storage hreach)).mp hreach
        exact ⟨z, hzw, hzt, by intro h; cases h⟩
      | true =>
        obtain ⟨z, hzw, hzQ, hzt⟩ :=
          (reachD2_iff (b-d) wr Qr tr (reachD2_storage hreach)).mp hreach
        exact ⟨z, hzw, hzt, fun _ => hzQ⟩
    let y := completePQ d hd x z
    have hpref : «prefix» d y = «prefix» d x := prefix_completePQ d hd x z
    have hsuf : suffixPQ d hd y = z := suffix_completePQ d hd x z
    have hwy : weight y = weight («prefix» d x) + wr := by
      rw [weight_prefix_suffix d hd y, hpref, hsuf, hzw]
    have hqy (hl : load = true) : qSum y = qSum («prefix» d x) + Qr := by
      rw [qSum_prefix_suffix d hd y, hpref, hsuf, hzQ hl]
    have hty : theta y = prefixTheta d x + tr := by
      rw [theta_prefix_suffix d hd y, prefixTheta_congr d y x hpref, hsuf, hzt]
    have htarget' : targetTheta b s = m4 b s - (if b = 4 then 4 else 0) := by
      simp only [targetTheta, ite_eq_left he]
    rw [htcast, htarget'] at htarget
    refine ⟨y, by omega, hpref, s, hs, ?_, ?_, ?_, ?_⟩
    · simp only [ite_eq_left he]
      linarith
    · simp only [ite_eq_left he, hwy, Nat.cast_add]
      simpa only [Nat.cast_add, add_assoc] using hs2
    · intro hl
      have h := hload hl
      simp only [ite_eq_left he, hwy, hqy hl, Nat.cast_add]
      linarith
    · intro h
      cases h
  · rintro ⟨y, hbudget, hpref, s, hs, hm4, hs2, hload, _hcount⟩
    let z := suffixPQ d hd y
    have hwy : weight y = weight («prefix» d x) + weight z := by
      rw [weight_prefix_suffix d hd y, hpref]
    have hqy : qSum y = qSum («prefix» d x) + qSum z := by
      rw [qSum_prefix_suffix d hd y, hpref]
    have hty : theta y = prefixTheta d x + theta z := by
      rw [theta_prefix_suffix d hd y, prefixTheta_congr d y x hpref]
    have hznonneg := theta_nonneg z
    have htrcast : ((theta z).toNat : ℤ) = theta z := Int.toNat_of_nonneg hznonneg
    have htr : (theta z).toNat < 3072 := by
      have htotal := theta_lt_storage_bound b N y hbudget hN
      have hpnonneg := prefixTheta_nonneg d x
      omega
    have hwr : weight («prefix» d x) + weight z ≤ N-b := by omega
    have hQr : qSum z ≤ (N-b)/2 := by
      have hq : 2 * qSum z ≤ weight z := by unfold weight; omega
      omega
    refine ⟨htlt, s, hs, he, weight z, qSum z, (theta z).toNat, hwr, hQr, ?_, ?_, ?_, ?_⟩
    · cases load with
      | false =>
        change reachD1 (b-d) (weight z) (theta z).toNat
        exact (reachD1_iff (b-d) (weight z) (theta z).toNat htr).mpr
          ⟨z, rfl, htrcast.symm⟩
      | true =>
        change reachD2 (b-d) (weight z) (qSum z) (theta z).toNat
        exact (reachD2_iff (b-d) (weight z) (qSum z) (theta z).toNat htr).mpr
          ⟨z, rfl, rfl, htrcast.symm⟩
    · simp only [targetTheta, ite_eq_left he, htcast, htrcast]
      simp only [ite_eq_left he] at hm4
      linarith
    · simp only [ite_eq_left he, hwy, Nat.cast_add] at hs2
      simpa only [Nat.cast_add, add_assoc] using hs2
    · intro hl
      have h := hload hl
      simp only [ite_eq_left he, hwy, hqy, Nat.cast_add] at h
      linarith
#print axioms Paper7Pruning.dReachable_completion_iff

end Paper7Pruning
