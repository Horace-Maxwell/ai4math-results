import Research.Backfill.Paper7.IntegerSpectrum
import Research.Backfill.Paper7.Lemma23

/-! Both original divisibility clauses, for every finite integral graph. -/
set_option autoImplicit false
noncomputable section
namespace Paper7OddIntegral
open BackfillPaper7.Challenge

theorem oddGirth_three_le {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {g : ℕ} (hg : IsOddGirth G g) : 3 ≤ g := by
  obtain ⟨u, w, hw, hlen⟩ := hg.2.1
  simpa only [hlen] using hw.three_le_length
#print axioms Paper7OddIntegral.oddGirth_three_le

/-- Fermat periodicity includes residues divisible by the prime. -/
theorem integer_pow_sub_dvd (q g : ℕ) (hq : q.Prime) (hg : 0 < g)
    (hperiod : q - 1 ∣ g - 1) (z : ℤ) : (q : ℤ) ∣ z ^ g - z := by
  let : Fact q.Prime := ⟨hq⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (z ^ g - z) q).mp
  push_cast
  apply sub_eq_zero.mpr
  by_cases hz : (z : ZMod q) = 0
  · simp only [hz, zero_pow (by omega : g ≠ 0)]
  · obtain ⟨k, hk⟩ := hperiod
    have hgk : g = (q - 1) * k + 1 := by omega
    rw [hgk, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hz, one_pow,
      pow_one, one_mul]
#print axioms Paper7OddIntegral.integer_pow_sub_dvd

theorem integral_trace_period_divisibility {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (q g : ℕ) (hq : q.Prime) (hg : 0 < g) (hperiod : q - 1 ∣ g - 1) :
    (q : ℤ) ∣ ((G.adjMatrix ℤ) ^ g).trace := by
  have hsum : ((integerSpectrum G).map (fun z => z ^ g - z)).sum =
      ((G.adjMatrix ℤ) ^ g).trace := by
    rw [Multiset.sum_map_sub, integerSpectrum_moment G hG g,
      Multiset.map_id', integerSpectrum_sum G hG, sub_zero]
  rw [← hsum]
  apply Multiset.dvd_sum
  intro z hz
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hz
  exact integer_pow_sub_dvd q g hq hg hperiod x
#print axioms Paper7OddIntegral.integral_trace_period_divisibility

theorem proposition3_prime_divisibility {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ)
    (hG : IsIntegralGraph G) (hg : IsOddGirth G g) :
    ∀ q : ℕ, q.Prime → (q - 1) ∣ (g - 1) → q ∣ 2 * g * cycleCount G g := by
  intro q hq hperiod
  have h := integral_trace_period_divisibility G hG q g hq
    (by have := oddGirth_three_le hg; omega) hperiod
  rw [Paper7Moments.trace_oddGirth G hg] at h
  exact_mod_cast h
#print axioms Paper7OddIntegral.proposition3_prime_divisibility

theorem proposition3_three_divisibility {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ)
    (hG : IsIntegralGraph G) (hg : IsOddGirth G g) : 3 ∣ g * cycleCount G g := by
  have hperiod : 3 - 1 ∣ g - 1 := by
    obtain ⟨k, hk⟩ := hg.1
    exact ⟨k, by omega⟩
  have h := proposition3_prime_divisibility G g hG hg 3 Nat.prime_three hperiod
  rw [mul_assoc] at h
  rcases Nat.prime_three.dvd_mul.mp h with h2 | hprod
  · norm_num at h2
  · exact hprod
#print axioms Paper7OddIntegral.proposition3_three_divisibility

end Paper7OddIntegral
