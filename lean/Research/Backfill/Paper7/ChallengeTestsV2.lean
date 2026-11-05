import Research.Backfill.Paper7.ChallengeV2

/-!
# Known-answer tests for the custom definitions of `Challenge.lean` (Paper 7)

Addendum 1, item 2.  Every test reproduces a value stated in the paper (or in the cited
[bms]/[brt]) or a small case, and some tests check that a wrong value is rejected.
Only kernel-checked tactics are used (`decide`, `decide +kernel`, `rfl`, `norm_num`, `simp`).
Tests of the spectral definitions (`eigs`, `spec`, `Ngt`, `mult`, `IsIntegralGraph`, …) and of
the walk-based definitions (`cycleCount`, `IsOddGirth`, `IsUnicyclicWithCycle`) need real proofs;
they are listed in `work/lean-backfill/paper7/STATEMENTS.md` (§ "Definitions the reader must
trust") and scheduled for phase 2.
-/

set_option autoImplicit false

namespace BackfillPaper7.Challenge

/-! ### `sunGraph`, `sunRel`, `SunV` -/

-- the cycle of `C_{6,1}(0,6,6,12,6,6)`: v0 ~ v1, v5 ~ v0 (wrap-around), v0 ≁ v2, v0 ≁ v3
theorem test_001 : (sunGraph 6 C61).Adj (Sum.inl 0) (Sum.inl 1) := by decide
theorem test_002 : (sunGraph 6 C61).Adj (Sum.inl 5) (Sum.inl 0) := by decide
theorem test_003 : ¬ (sunGraph 6 C61).Adj (Sum.inl 0) (Sum.inl 2) := by decide
theorem test_004 : ¬ (sunGraph 6 C61).Adj (Sum.inl 0) (Sum.inl 3) := by decide
-- no loops
theorem test_005 : ¬ (sunGraph 6 C61).Adj (Sum.inl 2) (Sum.inl 2) := by decide
-- a pendant vertex at v1 is adjacent to v1 only
theorem test_006 : (sunGraph 6 C61).Adj (Sum.inl 1) (Sum.inr ⟨1, ⟨0, by decide⟩, ⟨0, by decide⟩⟩) := by decide
theorem test_007 : ¬ (sunGraph 6 C61).Adj (Sum.inl 2) (Sum.inr ⟨1, ⟨0, by decide⟩, ⟨0, by decide⟩⟩) := by decide
-- a pendant `P_2` of `C_{4,2}(4,4,0,0)` at v0: v0 ~ w, w ~ w', v0 ≁ w'
theorem test_008 : (sunGraph 4 G20b).Adj (Sum.inl 0) (Sum.inr ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩) := by decide
theorem test_009 : (sunGraph 4 G20b).Adj (Sum.inr ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩)
    (Sum.inr ⟨0, ⟨0, by decide⟩, ⟨1, by decide⟩⟩) := by decide
theorem test_010 : ¬ (sunGraph 4 G20b).Adj (Sum.inl 0) (Sum.inr ⟨0, ⟨0, by decide⟩, ⟨1, by decide⟩⟩) := by decide
-- two different pendant paths at the same vertex are not adjacent to each other
theorem test_011 : ¬ (sunGraph 4 G20b).Adj (Sum.inr ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩)
    (Sum.inr ⟨0, ⟨1, by decide⟩, ⟨0, by decide⟩⟩) := by decide

/-! ### `order`, `pendantCount` (paper: 42, 13, 20, 20 vertices) -/

theorem test_012 : order 6 C61 = 42 := by decide +kernel
theorem test_013 : order 4 G13 = 13 := by decide +kernel
theorem test_014 : order 4 G20a = 20 := by decide +kernel
theorem test_015 : order 4 G20b = 20 := by decide +kernel
theorem test_016 : order 6 C61 ≠ 41 := by decide +kernel
theorem test_017 : pendantCount 6 C61 = 36 := by decide
theorem test_018 : pendantCount 4 G20a = 16 := by decide
-- a bare cycle is "a cycle": no pendant vertex
theorem test_019 : pendantCount 5 (fun _ => []) = 0 := by decide
-- the `P_1/P_2` encoding reproduces the named graphs
theorem test_020 : pq 6 ![0, 6, 6, 12, 6, 6] ![0, 0, 0, 0, 0, 0] = C61 := by decide
theorem test_021 : pq 4 ![0, 1, 0, 1] ![5, 0, 2, 0] = G20a := by decide
theorem test_022 : pq 4 ![0, 0, 0, 0] ![4, 4, 0, 0] = G20b := by decide
theorem test_023 : nOf 6 ![0, 6, 6, 12, 6, 6] ![0, 0, 0, 0, 0, 0] = 42 := by decide

/-! ### `kappa` (paper: κ_b = 30, 42, 30, 66, 2730 for b = 5, 7, 9, 11, 13; κ_b ∣ 2b for b = 3, 15) -/

theorem test_024 : kappa 5 = 30 := by decide +kernel
theorem test_025 : kappa 7 = 42 := by decide +kernel
theorem test_026 : kappa 9 = 30 := by decide +kernel
theorem test_027 : kappa 11 = 66 := by decide +kernel
theorem test_028 : kappa 13 = 2730 := by decide +kernel
theorem test_029 : kappa 3 ∣ 2 * 3 := by decide +kernel
theorem test_030 : kappa 15 ∣ 2 * 15 := by decide +kernel
theorem test_031 : ¬ kappa 9 ∣ 2 * 9 := by decide +kernel

/-! ### `sigmaSq` (paper: σ(9) = 68, σ(10) = 84, σ(11) = 100, σ(14) = 166; σ(t) = 0 for t ≤ 0) -/

theorem test_032 : sigmaSq 9 = 68 ∧ sigmaSq 10 = 84 ∧ sigmaSq 11 = 100 ∧ sigmaSq 14 = 166 := by decide
theorem test_033 : sigmaSq 0 = 0 ∧ sigmaSq (-3) = 0 := by decide
theorem test_034 : sigmaSq 10 ≠ 83 := by decide

/-! ### `Kp`, `Kq`, `evenGaps`, `delta0`, `inGap`
Known answers from Lemma 2.2(b), `mult(0) = P - |K_p| + δ_0`, against the stated spectra:
`C_{6,1}(0,6,6,12,6,6)`: 36 - 5 + 1 = 32 = mult(0);  `C_{4,1}(6,0,3,0)`: 9 - 2 + 2 = 9;
`C_4(5P_2,P_1,2P_2,P_1)`: 2 - 2 + 2 = 2;  `C_{4,2}(4,4,0,0)`: `K_p = ∅`, `4 ∣ 4`, so 0 - 0 + 2 = 2. -/

theorem test_035 : Kp 6 ![0, 6, 6, 12, 6, 6] = {1, 2, 3, 4, 5} := by decide
theorem test_036 : delta0 6 ![0, 6, 6, 12, 6, 6] = 1 := by decide
theorem test_037 : delta0 4 ![6, 0, 3, 0] = 2 := by decide
theorem test_038 : delta0 4 ![0, 1, 0, 1] = 2 := by decide
theorem test_039 : delta0 4 ![0, 0, 0, 0] = 2 := by decide
theorem test_040 : delta0 6 ![0, 0, 0, 0, 0, 0] = 0 := by decide
theorem test_041 : delta0 6 ![0, 6, 6, 12, 6, 6] ≠ 0 := by decide
-- |K| = 1: the only gap has length b
theorem test_042 : evenGaps 6 {0} = 1 ∧ evenGaps 5 {0} = 0 := by decide
theorem test_043 : evenGaps 6 {0, 3} = 0 ∧ evenGaps 6 {0, 2, 4} = 3 := by decide
theorem test_044 : Kq 4 ![5, 0, 2, 0] = {0, 2} := by decide
theorem test_045 : inGap 6 {0, 3} 0 1 ∧ inGap 6 {0, 3} 0 2 ∧ ¬ inGap 6 {0, 3} 0 3 ∧ ¬ inGap 6 {0, 3} 0 4 := by
  unfold inGap; decide

/-! ### `thetaV` (identity (1): `Θ(C_{6,1}(0,6,6,12,6,6)) = ∑_{B^+} λ²(λ²-1) = 16·15 + 2·9·8 + 2·4·3 = 408`) -/

theorem test_046 : ∑ k : Fin 6, thetaV (![0, 6, 6, 12, 6, 6] k) 0 = 408 := by decide
-- `C_{4,1}(6,0,3,0)`: 2Θ + 8 = 2(9·8 + 4·3) = 168, i.e. Θ = 80
theorem test_047 : ∑ k : Fin 4, thetaV (![6, 0, 3, 0] k) 0 = 80 := by decide
theorem test_048 : ∑ k : Fin 6, thetaV (![0, 6, 6, 12, 6, 6] k) 0 ≠ 407 := by decide

/-! ### `Xset`, `gW` -/

theorem test_049 : Xset 5 = {0, 1, 2, 3} := by decide
theorem test_050 : gW 0 = 2 ∧ gW 3 = 20 := by decide

end BackfillPaper7.Challenge

#print axioms BackfillPaper7.Challenge.test_001
#print axioms BackfillPaper7.Challenge.test_002
#print axioms BackfillPaper7.Challenge.test_003
#print axioms BackfillPaper7.Challenge.test_004
#print axioms BackfillPaper7.Challenge.test_005
#print axioms BackfillPaper7.Challenge.test_006
#print axioms BackfillPaper7.Challenge.test_007
#print axioms BackfillPaper7.Challenge.test_008
#print axioms BackfillPaper7.Challenge.test_009
#print axioms BackfillPaper7.Challenge.test_010
#print axioms BackfillPaper7.Challenge.test_011
#print axioms BackfillPaper7.Challenge.test_012
#print axioms BackfillPaper7.Challenge.test_013
#print axioms BackfillPaper7.Challenge.test_014
#print axioms BackfillPaper7.Challenge.test_015
#print axioms BackfillPaper7.Challenge.test_016
#print axioms BackfillPaper7.Challenge.test_017
#print axioms BackfillPaper7.Challenge.test_018
#print axioms BackfillPaper7.Challenge.test_019
#print axioms BackfillPaper7.Challenge.test_020
#print axioms BackfillPaper7.Challenge.test_021
#print axioms BackfillPaper7.Challenge.test_022
#print axioms BackfillPaper7.Challenge.test_023
#print axioms BackfillPaper7.Challenge.test_024
#print axioms BackfillPaper7.Challenge.test_025
#print axioms BackfillPaper7.Challenge.test_026
#print axioms BackfillPaper7.Challenge.test_027
#print axioms BackfillPaper7.Challenge.test_028
#print axioms BackfillPaper7.Challenge.test_029
#print axioms BackfillPaper7.Challenge.test_030
#print axioms BackfillPaper7.Challenge.test_031
#print axioms BackfillPaper7.Challenge.test_032
#print axioms BackfillPaper7.Challenge.test_033
#print axioms BackfillPaper7.Challenge.test_034
#print axioms BackfillPaper7.Challenge.test_035
#print axioms BackfillPaper7.Challenge.test_036
#print axioms BackfillPaper7.Challenge.test_037
#print axioms BackfillPaper7.Challenge.test_038
#print axioms BackfillPaper7.Challenge.test_039
#print axioms BackfillPaper7.Challenge.test_040
#print axioms BackfillPaper7.Challenge.test_041
#print axioms BackfillPaper7.Challenge.test_042
#print axioms BackfillPaper7.Challenge.test_043
#print axioms BackfillPaper7.Challenge.test_044
#print axioms BackfillPaper7.Challenge.test_045
#print axioms BackfillPaper7.Challenge.test_046
#print axioms BackfillPaper7.Challenge.test_047
#print axioms BackfillPaper7.Challenge.test_048
#print axioms BackfillPaper7.Challenge.test_049
#print axioms BackfillPaper7.Challenge.test_050
