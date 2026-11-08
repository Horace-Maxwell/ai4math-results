import Research.Backfill.Paper1.TightFamilies
import Research.Backfill.Paper1.EqualParityMax
import Research.Backfill.Paper1.SignTwo

/-! Full frozen Remark17: actual simple-graph energy of the five-element set
and the complete maximum statement. Acceptance evidence is recorded separately. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace NearMax

def nearSet (p : ℕ) : Finset ℕ := {1, 3, p ^ 2, 3 * p ^ 2, 9 * p}

lemma mem_nearSet {p : ℕ} (hp : p.Prime) (hne : p ≠ 3) (i j : ℕ) :
    p ^ i * 3 ^ j ∈ nearSet p ↔
      (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 0) ∨
        (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  have hd : nearSet p =
      {p ^ 0 * 3 ^ 0, p ^ 0 * 3 ^ 1, p ^ 2 * 3 ^ 0, p ^ 2 * 3 ^ 1, p ^ 1 * 3 ^ 2} := by
    simp [nearSet, mul_comm]
  rw [hd]
  simp only [Finset.mem_insert, Finset.mem_singleton, pq_inj hp Nat.prime_three hne]

lemma near_sign {p : ℕ} (hp : p.Prime) (hne : p ≠ 3) :
    ∀ i ≤ 2, ∀ j ≤ 2,
      2 * (if p ^ i * 3 ^ j ∈ nearSet p then (1 : ℝ) else 0) - 1 =
        Challenge.sAlt i * Challenge.g2 j := by
  intro i hi j hj
  simp only [mem_nearSet hp hne]
  interval_cases i <;> interval_cases j <;> norm_num [Challenge.sAlt, Challenge.g2]

lemma near_energy {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Challenge.energy (p ^ 2 * 3 ^ 2) (nearSet p) =
      62 * (p : ℝ) ^ 2 - 90 * p + 40 - 2 * ((p : ℝ) - 3) := by
  have hne : p ≠ 3 := by omega
  have hpR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hND : p ^ 2 * 3 ^ 2 ∉ nearSet p := by
    rw [mem_nearSet hp hne]
    norm_num
  have h := ICGEqualParityB.two_energy hp Nat.prime_three hne (by omega) le_rfl 2 (nearSet p)
  rw [← GraphBridge.graph_energy_eq (p ^ 2 * 3 ^ 2) (nearSet p) hND] at h
  norm_num only [Nat.cast_ofNat] at h
  have hG := ICGEqualParityB.Gfun_congr (p := (p : ℝ)) (q := 3) (near_sign hp hne)
  rw [hG, ← SignTwo.Gval_eq_Gfun (by norm_num : (0 : ℝ) < 3),
    TightFamilies.first_G hpR, TightFamilies.dNorm_two hpR] at h
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
  nlinarith

end NearMax

theorem check_Remark17 : Challenge.Remark17 := by
  intro p hp hp5
  have hpq : Challenge.DistinctOddPrimes p 3 :=
    ⟨hp, Nat.prime_three, by omega, hp.odd_of_ne_two (by omega), by decide⟩
  refine ⟨NearMax.near_energy hp hp5, ?_⟩
  have h := (check_Theorem4 p 3 2 hpq (by decide) (by decide)).1
  norm_num only [Nat.cast_ofNat] at h
  have hV :
      (((((p ^ 2 * 3 ^ 2 : ℕ) : ℝ)) +
        (5 * (p : ℝ) ^ 2 - 8 * p + 4) * Challenge.dClosed 2 3) / 2 -
        ((p : ℝ) ^ 2 - 2 * p + 2) * Challenge.deltaK 2 3) =
      62 * (p : ℝ) ^ 2 - 90 * p + 40 := by
    norm_num [Challenge.dClosed, Challenge.deltaK, Finset.sum_range_succ]
    ring
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at hV ⊢
  rwa [hV] at h

#print axioms check_Remark17
end CodexPaper1
