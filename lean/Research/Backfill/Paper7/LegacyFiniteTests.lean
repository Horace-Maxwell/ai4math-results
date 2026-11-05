import Research.Backfill.Paper7.LegacyTestRequirements

/-! Local parser, finite-order, recurrence and polynomial controls only. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Paper7StatementTestsV3
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open BackfillPaper7.Challenge.Legacy.Algebra Polynomial

/-- Literal legacy split, proved through the core equation theorems. -/
theorem legacy_split_leaf_short :
    "LEAF 0,0".splitOn " " = ["LEAF", "0,0"] := by
  unfold String.splitOn
  cbv
#print axioms Paper7StatementTestsV3.legacy_split_leaf_short

theorem legacy_split_bad_pair : "a,2".splitOn "," = ["a", "2"] := by
  unfold String.splitOn
  cbv
#print axioms Paper7StatementTestsV3.legacy_split_bad_pair

theorem legacy_split_zero_pair : "0,0".splitOn "," = ["0", "0"] := by
  unfold String.splitOn
  cbv
#print axioms Paper7StatementTestsV3.legacy_split_zero_pair

theorem legacy_split_leaf_ten :
    "LEAF 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0".splitOn " " =
      ["LEAF", "0,0", "0,0", "0,0", "0,0", "0,0",
        "0,0", "0,0", "0,0", "0,0", "0,0"] := by
  unfold String.splitOn
  cbv
#print axioms Paper7StatementTestsV3.legacy_split_leaf_ten

/-- The original slice iterator and fold are connected to their list semantics. -/
theorem legacy_toNat_bad : "a".toNat? = none := by
  unfold String.toNat? String.Slice.toNat? String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList,
    String.Slice.foldl_eq_foldl_toList, String.copy_toSlice]
  cbv
#print axioms Paper7StatementTestsV3.legacy_toNat_bad

theorem legacy_toNat_zero : "0".toNat? = some 0 := by
  unfold String.toNat? String.Slice.toNat? String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList,
    String.Slice.foldl_eq_foldl_toList, String.copy_toSlice]
  cbv
#print axioms Paper7StatementTestsV3.legacy_toNat_zero

theorem test103 : BackfillPaper7.Challenge.LegacyTests.test_103_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_103_required
  have hsplit : "LEAF 0,0".splitOn " " = ["LEAF", "0,0"] :=
    legacy_split_leaf_short
  simp [parseLeaf, hsplit]
#print axioms Paper7StatementTestsV3.test103

theorem test104 : BackfillPaper7.Challenge.LegacyTests.test_104_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_104_required
  have hsplit : "a,2".splitOn "," = ["a", "2"] := legacy_split_bad_pair
  have ha : "a".toNat? = none := legacy_toNat_bad
  simp [parsePair, hsplit, ha]
#print axioms Paper7StatementTestsV3.test104

theorem test105 : BackfillPaper7.Challenge.LegacyTests.test_105_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_105_required
  have hsplit :
      "LEAF 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0".splitOn " " =
        ["LEAF", "0,0", "0,0", "0,0", "0,0", "0,0",
          "0,0", "0,0", "0,0", "0,0", "0,0"] := legacy_split_leaf_ten
  have hpair : parsePair "0,0" = some (0,0) := by
    have hs : "0,0".splitOn "," = ["0", "0"] := legacy_split_zero_pair
    have hn : "0".toNat? = some 0 := legacy_toNat_zero
    simp [parsePair, hs, hn]
  let pairs : List (ℕ × ℕ) :=
    [(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
  have hparse : parseLeaf "LEAF 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0" =
      some ((fun i : Fin 10 => (pairs.getD i.val (0,0)).1),
        (fun i : Fin 10 => (pairs.getD i.val (0,0)).2)) := by
    simp [parseLeaf, hsplit, hpair, pairs]
  rw [hparse]
  apply congrArg (some : PQ 10 → Option (PQ 10))
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
#print axioms Paper7StatementTestsV3.test105

theorem test106 : BackfillPaper7.Challenge.LegacyTests.test_106_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_106_required Budget
  decide +kernel
#print axioms Paper7StatementTestsV3.test106

theorem test107 : BackfillPaper7.Challenge.LegacyTests.test_107_required := by
  rintro ⟨⟨ρ,_,heq,_⟩,_⟩
  have hzero : (0 : Fin 3) = 1 := heq
  exact (by decide : (0 : Fin 3) ≠ 1) hzero
#print axioms Paper7StatementTestsV3.test107

theorem test108 : BackfillPaper7.Challenge.LegacyTests.test_108_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_108_required RotationRule
  decide +kernel
#print axioms Paper7StatementTestsV3.test108

/-- Replaces an unbounded shift witness by its exact residue for this Fin 3 test. -/
theorem dihedral_three_bounded (σ : Fin 3 → Fin 3) (h : IsDihedral 3 σ) :
    ∃ c : Fin 3,
      (∀ k, (σ k).val = (k.val + c.val) % 3) ∨
      (∀ k, ((σ k).val + k.val) % 3 = c.val) := by
  obtain ⟨c,hrot | href⟩ := h
  · refine ⟨⟨c%3, Nat.mod_lt _ (by decide)⟩, Or.inl ?_⟩
    intro k
    have hk := hrot k
    simpa only [Nat.add_mod_mod] using hk
  · exact ⟨⟨c%3, Nat.mod_lt _ (by decide)⟩, Or.inr href⟩
#print axioms Paper7StatementTestsV3.dihedral_three_bounded

theorem test109 : BackfillPaper7.Challenge.LegacyTests.test_109_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_109_required
  constructor
  · intro σ hσ
    have hfinite : ∀ σ : Fin 3 → Fin 3,
        (∃ c : Fin 3,
          (∀ k, (σ k).val = (k.val+c.val)%3) ∨
          (∀ k, ((σ k).val+k.val)%3=c.val)) →
        LexLE key1000 (![0,0,1], ![0,0,0])
          (reindex σ (![0,0,1], ![0,0,0])) := by
      unfold LexLE
      decide +kernel
    exact hfinite σ (dihedral_three_bounded σ hσ)
  · intro h
    have hσ : IsDihedral 3 (![2,0,1] : Fin 3 → Fin 3) := by
      exact ⟨2, Or.inl (by decide)⟩
    have hx := h (![2,0,1] : Fin 3 → Fin 3) hσ
    have hbad : ¬ LexLE key1000
        (reindex (![2,0,1] : Fin 3 → Fin 3) (![0,0,1], ![0,0,0]))
        (![0,0,1], ![0,0,0]) := by
      unfold LexLE
      decide +kernel
    exact hbad hx
#print axioms Paper7StatementTestsV3.test109

theorem test110 : BackfillPaper7.Challenge.LegacyTests.test_110_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_110_required reachD1
  decide +kernel
#print axioms Paper7StatementTestsV3.test110

theorem test111 : BackfillPaper7.Challenge.LegacyTests.test_111_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_111_required
  constructor
  · exact ⟨by decide,0,1,by decide,by decide,0,by decide,by norm_num [reachD2]⟩
  · rintro ⟨_,p,q,hw,hq,u,hu,hbase⟩
    have hq0 : q = 0 := by omega
    subst q
    have hp : p ≤ 2 := by omega
    interval_cases p <;> norm_num [reachD2,thetaV] at *
    omega
#print axioms Paper7StatementTestsV3.test111

theorem test112 : BackfillPaper7.Challenge.LegacyTests.test_112_required := by
  rintro ⟨hcut,_⟩
  omega
#print axioms Paper7StatementTestsV3.test112

theorem test113 : BackfillPaper7.Challenge.LegacyTests.test_113_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_113_required
  decide +kernel
#print axioms Paper7StatementTestsV3.test113

theorem test116 : BackfillPaper7.Challenge.LegacyTests.test_116_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_116_required
  decide +kernel
#print axioms Paper7StatementTestsV3.test116

theorem test118 : BackfillPaper7.Challenge.LegacyTests.test_118_required := by
  change clearedF 3 (0 : Fin 3 → ℕ) (0 : Fin 3 → ℕ) = _
  have hA : cycleAdjZ 3 = (!![0,1,1; 1,0,1; 1,1,0] : Matrix (Fin 3) (Fin 3) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;>
      decide
  norm_num [clearedF, Matrix.det_fin_three, clearedMatrix, hA]
  ring
#print axioms Paper7StatementTestsV3.test118

theorem test119 : BackfillPaper7.Challenge.LegacyTests.test_119_required := by
  unfold BackfillPaper7.Challenge.LegacyTests.test_119_required
  rfl
#print axioms Paper7StatementTestsV3.test119

theorem test120 : BackfillPaper7.Challenge.LegacyTests.test_120_required := by
  simp [BackfillPaper7.Challenge.LegacyTests.test_120_required, integerMono,
    List.finRange_succ, mul_assoc]
#print axioms Paper7StatementTestsV3.test120

end Paper7StatementTestsV3
