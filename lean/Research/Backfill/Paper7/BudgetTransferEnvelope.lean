import Research.Backfill.Paper7.LegacyTransfer

/-! Integer envelope bounds on the actual frozen transfer factors.
These are helper candidates, not a proof of LegacyTransferCRTExactness. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CRTEnvelope
open BackfillPaper7.Challenge.Legacy

theorem budget_row_load_le (b N : ℕ) (x : PQ b) (hB : Budget b N x)
    (hN : N ≤ 49) (k : Fin b) : x.1 k + x.2 k ≤ 49 := by
  have hp : x.1 k ≤ pSum x :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (x.1 i)) (Finset.mem_univ k)
  have hq : x.2 k ≤ qSum x :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (x.2 i)) (Finset.mem_univ k)
  have hb := hB.2
  change b + (pSum x + 2 * qSum x) ≤ N at hb
  omega
#print axioms Paper7CRTEnvelope.budget_row_load_le

theorem ordinary_integer_square_bounds (m : ℤ)
    (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) : 4 ≤ m ^ 2 ∧ m ^ 2 ≤ 81 := by
  have hlo := (Int.natAbs_le_iff_sq_le (a := (2 : ℤ)) (b := m)).mp
    (by simpa using hm)
  have hhi := (Int.natAbs_le_iff_sq_le (a := m) (b := (9 : ℤ))).mp
    (by simpa using hM)
  norm_num at hlo hhi
  exact ⟨hlo, hhi⟩
#print axioms Paper7CRTEnvelope.ordinary_integer_square_bounds

theorem transferS_integer_bounds (b N : ℕ) (x : PQ b) (hB : Budget b N x)
    (hN : N ≤ 49) (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9)
    (k : Fin b) : -3969 ≤ transferS x m k ∧ transferS x m k ≤ 6480 := by
  have hs := ordinary_integer_square_bounds m hm hM
  have hp : (0 : ℤ) ≤ x.1 k := Int.natCast_nonneg _
  have hq : (0 : ℤ) ≤ x.2 k := Int.natCast_nonneg _
  have hload : (x.1 k : ℤ) + x.2 k ≤ 49 := by
    exact_mod_cast budget_row_load_le b N x hB hN k
  have hbase0 : 0 ≤ m ^ 2 * (m ^ 2 - 1) :=
    mul_nonneg (by omega) (by omega)
  have hbase1 : m ^ 2 * (m ^ 2 - 1) ≤ 6480 := by
    have h := mul_le_mul hs.2 (show m ^ 2 - 1 ≤ (80 : ℤ) by omega)
      (show 0 ≤ m ^ 2 - 1 by omega) (show (0 : ℤ) ≤ 81 by norm_num)
    norm_num at h
    exact h
  have hp0 : 0 ≤ (x.1 k : ℤ) * (m ^ 2 - 1) := mul_nonneg hp (by omega)
  have hq0 : 0 ≤ (x.2 k : ℤ) * m ^ 2 := mul_nonneg hq (by omega)
  have hp1 := mul_le_mul_of_nonneg_left (show m ^ 2 - 1 ≤ (81 : ℤ) by omega) hp
  have hq1 := mul_le_mul_of_nonneg_left hs.2 hq
  have hpend : (x.1 k : ℤ) * (m ^ 2 - 1) + (x.2 k : ℤ) * m ^ 2 ≤ 3969 := by
    nlinarith
  unfold transferS
  constructor <;> linarith
#print axioms Paper7CRTEnvelope.transferS_integer_bounds

theorem transferS_natAbs_le (b N : ℕ) (x : PQ b) (hB : Budget b N x)
    (hN : N ≤ 49) (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9)
    (k : Fin b) : (transferS x m k).natAbs ≤ 6480 := by
  have h := transferS_integer_bounds b N x hB hN m hm hM k
  have ha : |transferS x m k| ≤ 6480 := abs_le.mpr ⟨by omega, h.2⟩
  have hc : ((transferS x m k).natAbs : ℤ) ≤ 6480 := by
    simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hc
#print axioms Paper7CRTEnvelope.transferS_natAbs_le

theorem transferH_natAbs_le (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    (transferH m).natAbs ≤ 720 := by
  have hs := ordinary_integer_square_bounds m hm hM
  have he : ((m ^ 2 - 1).natAbs : ℤ) = m ^ 2 - 1 :=
    Int.natAbs_of_nonneg (by omega)
  have hcast : ((m ^ 2 - 1).natAbs : ℤ) ≤ 80 := by rw [he]; omega
  have ht : (m ^ 2 - 1).natAbs ≤ 80 := by exact_mod_cast hcast
  rw [transferH, Int.natAbs_mul]
  calc
    m.natAbs * (m ^ 2 - 1).natAbs ≤ 9 * 80 := Nat.mul_le_mul hM ht
    _ = 720 := by norm_num
#print axioms Paper7CRTEnvelope.transferH_natAbs_le

theorem envelope_factor_le (b N : ℕ) (x : PQ b) (hB : Budget b N x)
    (hN : N ≤ 49) (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9)
    (k : Fin b) :
    (transferS x m k).natAbs + (transferH m).natAbs ≤ 7200 ∧
    (transferS x m k).natAbs + (transferH m).natAbs ≤ (2 : ℕ) ^ 13 := by
  have hS := transferS_natAbs_le b N x hB hN m hm hM k
  have hH := transferH_natAbs_le m hm hM
  constructor
  · omega
  · calc
      _ ≤ 7200 := by omega
      _ ≤ (2 : ℕ) ^ 13 := by norm_num
#print axioms Paper7CRTEnvelope.envelope_factor_le

theorem rowEnvelope_le_two_pow (b N : ℕ) (x : PQ b) (hb : b ≤ 18)
    (hB : Budget b N x) (hN : N ≤ 49) (m : ℤ)
    (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) : rowEnvelope x m ≤ 2 ^ 234 := by
  calc
    rowEnvelope x m ≤ ∏ _k : Fin b, (2 : ℕ) ^ 13 := by
      unfold rowEnvelope
      apply Finset.prod_le_prod
      intro k _
      exact (envelope_factor_le b N x hB hN m hm hM k).2
    _ = ((2 : ℕ) ^ 13) ^ b := by simp
    _ ≤ ((2 : ℕ) ^ 13) ^ 18 := Nat.pow_le_pow_right (by norm_num) hb
    _ = 2 ^ 234 := by norm_num
#print axioms Paper7CRTEnvelope.rowEnvelope_le_two_pow

theorem transferH_power_le_two_pow (b : ℕ) (hb : b ≤ 18) (m : ℤ)
    (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    (transferH m).natAbs ^ b ≤ 2 ^ 234 := by
  have hH := transferH_natAbs_le m hm hM
  have hbase : (transferH m).natAbs ≤ (2 : ℕ) ^ 13 := by
    exact hH.trans (by norm_num)
  calc
    (transferH m).natAbs ^ b ≤ ((2 : ℕ) ^ 13) ^ b := Nat.pow_le_pow_left hbase b
    _ ≤ ((2 : ℕ) ^ 13) ^ 18 := Nat.pow_le_pow_right (by norm_num) hb
    _ = 2 ^ 234 := by norm_num
#print axioms Paper7CRTEnvelope.transferH_power_le_two_pow

/-- Complete small-cycle budget envelope. This does not assert a CRT equivalence. -/
theorem budget_envelope_bound (b N : ℕ) (x : PQ b) (hb : b ≤ 18)
    (hB : Budget b N x) (hN : N ≤ 49) (m : ℤ)
    (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    rowEnvelope x m ≤ 2 ^ 234 ∧ (transferH m).natAbs ^ b ≤ 2 ^ 234 ∧
    2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b ≤ 2 ^ 236 ∧
    2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b < 2 ^ 240 := by
  have hr := rowEnvelope_le_two_pow b N x hb hB hN m hm hM
  have hh := transferH_power_le_two_pow b hb m hm hM
  have he : 2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ b ≤ 2 ^ 236 := by
    calc
      _ ≤ 2 * (2 : ℕ) ^ 234 + 2 * (2 : ℕ) ^ 234 :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hr) (Nat.mul_le_mul_left 2 hh)
      _ = 2 ^ 236 := by norm_num
  exact ⟨hr, hh, he, he.trans_lt (by norm_num)⟩
#print axioms Paper7CRTEnvelope.budget_envelope_bound

/-- The separate 4/36 control is covered without inserting it in ReportedARun. -/
theorem control_four_thirtysix_envelope (x : PQ 4) (hB : Budget 4 36 x)
    (m : ℤ) (hm : 2 ≤ m.natAbs) (hM : m.natAbs ≤ 9) :
    2 * rowEnvelope x m + 2 * (transferH m).natAbs ^ 4 < 2 ^ 240 :=
  (budget_envelope_bound 4 36 x (by norm_num) hB (by norm_num) m hm hM).2.2.2
#print axioms Paper7CRTEnvelope.control_four_thirtysix_envelope

end Paper7CRTEnvelope
