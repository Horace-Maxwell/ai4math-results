import Research.Backfill.Paper4.Proof.TriangleFreeFingerprint
import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Exact fingerprints and pairwise non-isomorphism of the 59 representatives.
Each equality computes the fingerprint of the actual graph; literal separation
is combined with the general isomorphism-invariance theorem.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.TriangleFreeRepresentativeFingerprint
open TriangleFreeFingerprint TriangleFreeEnumerationFamily

def fingerprints : Fin 59 → Multiset ℕ := ![
  (([390, 2097153, 2097153, 2097153, 2097153, 2097153, 2097153] : List ℕ) : Multiset ℕ),
  (([513, 773, 262145, 262145, 262145, 262145, 262210] : List ℕ) : Multiset ℕ),
  (([4097, 4097, 4292, 32769, 32769, 32769, 32899] : List ℕ) : Multiset ℕ),
  (([513, 513, 1156, 32769, 32769, 32834, 32834] : List ℕ) : Multiset ℕ),
  (([513, 578, 708, 32769, 32769, 32769, 33282] : List ℕ) : Multiset ℕ),
  (([513, 4097, 4097, 4097, 4162, 4227, 4675] : List ℕ) : Multiset ℕ),
  (([643, 643, 4097, 4097, 4097, 4097, 8194] : List ℕ) : Multiset ℕ),
  (([513, 513, 578, 1091, 4097, 4162, 4610] : List ℕ) : Multiset ℕ),
  (([513, 578, 643, 1026, 4097, 4097, 4610] : List ℕ) : Multiset ℕ),
  (([513, 513, 513, 1539, 4162, 4162, 4162] : List ℕ) : Multiset ℕ),
  (([513, 513, 578, 578, 1026, 1026, 1026] : List ℕ) : Multiset ℕ),
  (([1026, 1221, 262145, 262145, 262145, 262658, 262658] : List ℕ) : Multiset ℕ),
  (([4097, 4610, 4740, 32769, 32769, 33282, 33347] : List ℕ) : Multiset ℕ),
  (([1091, 1156, 4097, 32769, 32769, 36866, 36866] : List ℕ) : Multiset ℕ),
  (([4097, 4097, 4097, 4675, 4675, 8194, 8259] : List ℕ) : Multiset ℕ),
  (([513, 1026, 1604, 32769, 32834, 33282, 33282] : List ℕ) : Multiset ℕ),
  (([1026, 1026, 1156, 32769, 32769, 33282, 33282] : List ℕ) : Multiset ℕ),
  (([513, 4097, 4162, 4610, 4610, 4675, 5123] : List ℕ) : Multiset ℕ),
  (([1026, 4097, 4097, 4610, 4610, 4675, 4675] : List ℕ) : Multiset ℕ),
  (([513, 1091, 1539, 4097, 4162, 8194, 8194] : List ℕ) : Multiset ℕ),
  (([1091, 1091, 4097, 4097, 4610, 4610, 8194] : List ℕ) : Multiset ℕ),
  (([1026, 4097, 4097, 4227, 4610, 4610, 5123] : List ℕ) : Multiset ℕ),
  (([1026, 1026, 1026, 1091, 4097, 4610, 4610] : List ℕ) : Multiset ℕ),
  (([513, 578, 1026, 1539, 4610, 4610, 4610] : List ℕ) : Multiset ℕ),
  (([513, 1026, 1026, 1539, 4162, 4610, 4610] : List ℕ) : Multiset ℕ),
  (([1026, 1026, 1026, 1026, 1026, 1026, 1026] : List ℕ) : Multiset ℕ),
  (([1539, 1669, 262145, 262145, 266242, 266242, 266242] : List ℕ) : Multiset ℕ),
  (([1604, 1604, 32769, 32769, 65538, 65538, 65538] : List ℕ) : Multiset ℕ),
  (([4097, 5123, 5188, 32769, 36866, 36866, 36931] : List ℕ) : Multiset ℕ),
  (([8194, 8194, 8324, 32769, 32769, 33795, 33795] : List ℕ) : Multiset ℕ),
  (([4097, 4097, 8194, 8259, 8259, 8707, 8707] : List ℕ) : Multiset ℕ),
  (([4610, 4610, 5188, 32769, 33282, 33282, 33795] : List ℕ) : Multiset ℕ),
  (([1539, 1604, 4610, 32769, 33282, 36866, 36866] : List ℕ) : Multiset ℕ),
  (([513, 1539, 2052, 32834, 36866, 36866, 36866] : List ℕ) : Multiset ℕ),
  (([4097, 4610, 4610, 4675, 5123, 8194, 8707] : List ℕ) : Multiset ℕ),
  (([4097, 4610, 4610, 5123, 5123, 8194, 8259] : List ℕ) : Multiset ℕ),
  (([1539, 4097, 4675, 5123, 8194, 8194, 8194] : List ℕ) : Multiset ℕ),
  (([513, 4162, 5123, 5123, 8194, 8194, 8707] : List ℕ) : Multiset ℕ),
  (([1026, 1026, 2052, 33282, 33282, 33282, 33282] : List ℕ) : Multiset ℕ),
  (([1026, 4610, 4610, 4610, 4610, 5123, 5123] : List ℕ) : Multiset ℕ),
  (([1026, 1539, 1539, 4610, 4610, 8194, 8194] : List ℕ) : Multiset ℕ),
  (([1539, 1539, 4610, 4610, 4610, 4610, 8194] : List ℕ) : Multiset ℕ),
  (([2052, 2117, 262145, 294914, 294914, 294914, 294914] : List ℕ) : Multiset ℕ),
  (([4097, 5636, 5636, 65538, 65538, 65538, 65603] : List ℕ) : Multiset ℕ),
  (([8194, 8707, 8772, 32769, 36866, 37379, 37379] : List ℕ) : Multiset ℕ),
  (([4097, 8194, 8259, 8707, 8707, 12291, 12291] : List ℕ) : Multiset ℕ),
  (([2052, 2052, 33282, 33282, 65538, 65538, 65538] : List ℕ) : Multiset ℕ),
  (([4610, 5123, 5636, 33282, 36866, 36866, 37379] : List ℕ) : Multiset ℕ),
  (([2052, 5123, 5123, 36866, 36866, 36866, 36866] : List ℕ) : Multiset ℕ),
  (([5123, 5123, 8194, 8194, 8194, 8707, 8707] : List ℕ) : Multiset ℕ),
  (([4610, 4610, 8194, 8707, 8707, 8707, 8707] : List ℕ) : Multiset ℕ),
  (([5123, 5123, 5123, 8194, 8194, 8194, 12291] : List ℕ) : Multiset ℕ),
  (([12291, 12291, 12356, 32769, 40963, 40963, 40963] : List ℕ) : Multiset ℕ),
  (([2565, 2565, 524290, 524290, 524290, 524290, 524290] : List ℕ) : Multiset ℕ),
  (([8194, 9220, 9220, 65538, 65538, 66051, 66051] : List ℕ) : Multiset ℕ),
  (([8707, 8707, 9220, 36866, 36866, 40963, 40963] : List ℕ) : Multiset ℕ),
  (([8194, 8707, 8707, 12291, 12291, 12291, 12291] : List ℕ) : Multiset ℕ),
  (([12291, 12804, 12804, 65538, 69635, 69635, 69635] : List ℕ) : Multiset ℕ),
  (([16388, 16388, 16388, 98307, 98307, 98307, 98307] : List ℕ) : Multiset ℕ)]

theorem fingerprint_00 : graphFingerprint (reps 7 0) = fingerprints 0 := by
  decide +kernel
theorem fingerprint_01 : graphFingerprint (reps 7 1) = fingerprints 1 := by
  decide +kernel
theorem fingerprint_02 : graphFingerprint (reps 7 2) = fingerprints 2 := by
  decide +kernel
theorem fingerprint_03 : graphFingerprint (reps 7 3) = fingerprints 3 := by
  decide +kernel
theorem fingerprint_04 : graphFingerprint (reps 7 4) = fingerprints 4 := by
  decide +kernel
theorem fingerprint_05 : graphFingerprint (reps 7 5) = fingerprints 5 := by
  decide +kernel
theorem fingerprint_06 : graphFingerprint (reps 7 6) = fingerprints 6 := by
  decide +kernel
theorem fingerprint_07 : graphFingerprint (reps 7 7) = fingerprints 7 := by
  decide +kernel
theorem fingerprint_08 : graphFingerprint (reps 7 8) = fingerprints 8 := by
  decide +kernel
theorem fingerprint_09 : graphFingerprint (reps 7 9) = fingerprints 9 := by
  decide +kernel
theorem fingerprint_10 : graphFingerprint (reps 7 10) = fingerprints 10 := by
  decide +kernel
theorem fingerprint_11 : graphFingerprint (reps 7 11) = fingerprints 11 := by
  decide +kernel
theorem fingerprint_12 : graphFingerprint (reps 7 12) = fingerprints 12 := by
  decide +kernel
theorem fingerprint_13 : graphFingerprint (reps 7 13) = fingerprints 13 := by
  decide +kernel
theorem fingerprint_14 : graphFingerprint (reps 7 14) = fingerprints 14 := by
  decide +kernel
theorem fingerprint_15 : graphFingerprint (reps 7 15) = fingerprints 15 := by
  decide +kernel
theorem fingerprint_16 : graphFingerprint (reps 7 16) = fingerprints 16 := by
  decide +kernel
theorem fingerprint_17 : graphFingerprint (reps 7 17) = fingerprints 17 := by
  decide +kernel
theorem fingerprint_18 : graphFingerprint (reps 7 18) = fingerprints 18 := by
  decide +kernel
theorem fingerprint_19 : graphFingerprint (reps 7 19) = fingerprints 19 := by
  decide +kernel
theorem fingerprint_20 : graphFingerprint (reps 7 20) = fingerprints 20 := by
  decide +kernel
theorem fingerprint_21 : graphFingerprint (reps 7 21) = fingerprints 21 := by
  decide +kernel
theorem fingerprint_22 : graphFingerprint (reps 7 22) = fingerprints 22 := by
  decide +kernel
theorem fingerprint_23 : graphFingerprint (reps 7 23) = fingerprints 23 := by
  decide +kernel
theorem fingerprint_24 : graphFingerprint (reps 7 24) = fingerprints 24 := by
  decide +kernel
theorem fingerprint_25 : graphFingerprint (reps 7 25) = fingerprints 25 := by
  decide +kernel
theorem fingerprint_26 : graphFingerprint (reps 7 26) = fingerprints 26 := by
  decide +kernel
theorem fingerprint_27 : graphFingerprint (reps 7 27) = fingerprints 27 := by
  decide +kernel
theorem fingerprint_28 : graphFingerprint (reps 7 28) = fingerprints 28 := by
  decide +kernel
theorem fingerprint_29 : graphFingerprint (reps 7 29) = fingerprints 29 := by
  decide +kernel
theorem fingerprint_30 : graphFingerprint (reps 7 30) = fingerprints 30 := by
  decide +kernel
theorem fingerprint_31 : graphFingerprint (reps 7 31) = fingerprints 31 := by
  decide +kernel
theorem fingerprint_32 : graphFingerprint (reps 7 32) = fingerprints 32 := by
  decide +kernel
theorem fingerprint_33 : graphFingerprint (reps 7 33) = fingerprints 33 := by
  decide +kernel
theorem fingerprint_34 : graphFingerprint (reps 7 34) = fingerprints 34 := by
  decide +kernel
theorem fingerprint_35 : graphFingerprint (reps 7 35) = fingerprints 35 := by
  decide +kernel
theorem fingerprint_36 : graphFingerprint (reps 7 36) = fingerprints 36 := by
  decide +kernel
theorem fingerprint_37 : graphFingerprint (reps 7 37) = fingerprints 37 := by
  decide +kernel
theorem fingerprint_38 : graphFingerprint (reps 7 38) = fingerprints 38 := by
  decide +kernel
theorem fingerprint_39 : graphFingerprint (reps 7 39) = fingerprints 39 := by
  decide +kernel
theorem fingerprint_40 : graphFingerprint (reps 7 40) = fingerprints 40 := by
  decide +kernel
theorem fingerprint_41 : graphFingerprint (reps 7 41) = fingerprints 41 := by
  decide +kernel
theorem fingerprint_42 : graphFingerprint (reps 7 42) = fingerprints 42 := by
  decide +kernel
theorem fingerprint_43 : graphFingerprint (reps 7 43) = fingerprints 43 := by
  decide +kernel
theorem fingerprint_44 : graphFingerprint (reps 7 44) = fingerprints 44 := by
  decide +kernel
theorem fingerprint_45 : graphFingerprint (reps 7 45) = fingerprints 45 := by
  decide +kernel
theorem fingerprint_46 : graphFingerprint (reps 7 46) = fingerprints 46 := by
  decide +kernel
theorem fingerprint_47 : graphFingerprint (reps 7 47) = fingerprints 47 := by
  decide +kernel
theorem fingerprint_48 : graphFingerprint (reps 7 48) = fingerprints 48 := by
  decide +kernel
theorem fingerprint_49 : graphFingerprint (reps 7 49) = fingerprints 49 := by
  decide +kernel
theorem fingerprint_50 : graphFingerprint (reps 7 50) = fingerprints 50 := by
  decide +kernel
theorem fingerprint_51 : graphFingerprint (reps 7 51) = fingerprints 51 := by
  decide +kernel
theorem fingerprint_52 : graphFingerprint (reps 7 52) = fingerprints 52 := by
  decide +kernel
theorem fingerprint_53 : graphFingerprint (reps 7 53) = fingerprints 53 := by
  decide +kernel
theorem fingerprint_54 : graphFingerprint (reps 7 54) = fingerprints 54 := by
  decide +kernel
theorem fingerprint_55 : graphFingerprint (reps 7 55) = fingerprints 55 := by
  decide +kernel
theorem fingerprint_56 : graphFingerprint (reps 7 56) = fingerprints 56 := by
  decide +kernel
theorem fingerprint_57 : graphFingerprint (reps 7 57) = fingerprints 57 := by
  decide +kernel
theorem fingerprint_58 : graphFingerprint (reps 7 58) = fingerprints 58 := by
  decide +kernel

theorem fingerprints_correct (i : Fin 59) :
    graphFingerprint (reps 7 i) = fingerprints i := by
  fin_cases i
  · exact fingerprint_00
  · exact fingerprint_01
  · exact fingerprint_02
  · exact fingerprint_03
  · exact fingerprint_04
  · exact fingerprint_05
  · exact fingerprint_06
  · exact fingerprint_07
  · exact fingerprint_08
  · exact fingerprint_09
  · exact fingerprint_10
  · exact fingerprint_11
  · exact fingerprint_12
  · exact fingerprint_13
  · exact fingerprint_14
  · exact fingerprint_15
  · exact fingerprint_16
  · exact fingerprint_17
  · exact fingerprint_18
  · exact fingerprint_19
  · exact fingerprint_20
  · exact fingerprint_21
  · exact fingerprint_22
  · exact fingerprint_23
  · exact fingerprint_24
  · exact fingerprint_25
  · exact fingerprint_26
  · exact fingerprint_27
  · exact fingerprint_28
  · exact fingerprint_29
  · exact fingerprint_30
  · exact fingerprint_31
  · exact fingerprint_32
  · exact fingerprint_33
  · exact fingerprint_34
  · exact fingerprint_35
  · exact fingerprint_36
  · exact fingerprint_37
  · exact fingerprint_38
  · exact fingerprint_39
  · exact fingerprint_40
  · exact fingerprint_41
  · exact fingerprint_42
  · exact fingerprint_43
  · exact fingerprint_44
  · exact fingerprint_45
  · exact fingerprint_46
  · exact fingerprint_47
  · exact fingerprint_48
  · exact fingerprint_49
  · exact fingerprint_50
  · exact fingerprint_51
  · exact fingerprint_52
  · exact fingerprint_53
  · exact fingerprint_54
  · exact fingerprint_55
  · exact fingerprint_56
  · exact fingerprint_57
  · exact fingerprint_58

theorem fingerprints_injective : Function.Injective fingerprints := by decide +kernel

theorem representatives_pairwise (i j : Fin 59)
    (h : Nonempty (reps 7 i ≃g reps 7 j)) : i = j := by
  obtain ⟨e⟩ := h
  apply fingerprints_injective
  have he := graphFingerprint_iso e
  rw [fingerprints_correct j, fingerprints_correct i] at he
  exact he.symm

#print axioms fingerprints_correct
#print axioms representatives_pairwise

end CodexPaper4.TriangleFreeRepresentativeFingerprint
