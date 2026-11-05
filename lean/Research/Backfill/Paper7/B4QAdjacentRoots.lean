import Research.Backfill.Paper7.B4PerronBounds

/-! SOURCE ONLY. Ordinary roots and both integer square roots for p = 0 and
q supported at the adjacent positions 0 and 1. The second integer root is
derived from the actual spectrum. No spectral profile is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem qadjacent_four_trace_equation (a b m : ℝ) (hm : m ^ 2 - 1 ≠ 0) :
    (m ^ 2 - 1) *
      ((realFourProduct (m - a * m / (m ^ 2 - 1))
        (m - b * m / (m ^ 2 - 1)) m m).trace - 2) =
      m ^ 2 * (m ^ 4 - (a + b + 5) * m ^ 2 + (a + 2) * (b + 2)) := by
  rw [real_four_trace]
  field_simp [hm]
  ring
#print axioms Paper7B4Analytic.qadjacent_four_trace_equation

theorem qadjacent_ordinary_spec_iff (q : Fin 4 → ℕ)
    (hq2 : q 2 = 0) (hq3 : q 3 = 0) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 (fun _ => 0) q) ↔
      m ^ 4 - ((q 0 : ℝ) + q 1 + 5) * m ^ 2 +
        ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2) = 0 := by
  have hm : m ^ 2 - 1 ≠ 0 := by
    intro h
    have hh : (m - 1) * (m + 1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hh with hh | hh
    · exact hm1 (by linarith)
    · exact hmn (by linarith)
  have he : (m ^ 2 - 1) * ((Mono 4 (fun _ => 0) q m).trace - 2) =
      m ^ 2 * (m ^ 4 - ((q 0 : ℝ) + q 1 + 5) * m ^ 2 +
        ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2)) := by
    rw [mono_four_product]
    simpa [fk, hq2, hq3] using qadjacent_four_trace_equation (q 0) (q 1) m hm
  rw [← ordinary_trace_iff_spec (fun _ => 0) q m hmn hm0 hm1]
  constructor
  · intro ht
    rw [ht] at he
    have hz : m ^ 2 * (m ^ 4 - ((q 0 : ℝ) + q 1 + 5) * m ^ 2 +
        ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2)) = 0 := by linarith only [he]
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hm0)
  · intro hf
    rw [hf] at he
    have ht : (Mono 4 (fun _ => 0) q m).trace - 2 = 0 :=
      (mul_eq_zero.mp (by simpa only [mul_zero] using he)).resolve_left hm
    linarith only [ht]
#print axioms Paper7B4Analytic.qadjacent_ordinary_spec_iff

theorem qadjacent_two_integer_roots (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, ((0 : ℕ) + q k))
    (hG : IsIntegralGraph (SG 4 (fun _ => 0) q))
    (hq2 : q 2 = 0) (hq3 : q 3 = 0) :
    ∃ R S : ℕ, 3 ≤ R ∧ 2 ≤ S ∧ S < R ∧
      q 0 + q 1 + 5 = R ^ 2 + S ^ 2 ∧
      (q 0 + 2) * (q 1 + 2) = R ^ 2 * S ^ 2 := by
  obtain ⟨R, hR, hmem, _hbound, hcap⟩ :=
    integral_perron_load_data (fun _ => 0) q hq hG
  have hRr : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hpoly := (qadjacent_ordinary_spec_iff q hq2 hq3 R
    (by linarith) (by linarith) (by linarith)).mp hmem
  have hposN : 0 < q 0 + q 1 := by
    simpa only [Fin.sum_univ_four, Nat.zero_add, hq2, hq3, Nat.add_zero] using hq
  have hpos : (0 : ℝ) < q 0 + q 1 := by exact_mod_cast hposN
  have hab : (0 : ℝ) ≤ (q 0 : ℝ) * q 1 := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let t : ℝ := (q 0 : ℝ) + q 1 + 5 - (R : ℝ) ^ 2
  have hsum : (q 0 : ℝ) + q 1 + 5 = (R : ℝ) ^ 2 + t := by dsimp [t]; ring
  have hRfour : (R : ℝ) ^ 4 = ((R : ℝ) ^ 2) ^ 2 := by ring
  have hprod : (R : ℝ) ^ 2 * t = ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2) := by
    dsimp [t]
    nlinarith only [hpoly, hRfour]
  have hsign : ((R : ℝ) ^ 2 - 1) * (t - 1) =
      (q 0 : ℝ) * q 1 + q 0 + q 1 := by
    nlinarith only [hsum, hprod]
  have ht : 1 < t := by
    by_contra h
    have hleft : 0 ≤ (R : ℝ) ^ 2 - 1 := by nlinarith
    have hright : 0 ≤ 1 - t := by linarith
    have hmul := mul_nonneg hleft hright
    nlinarith only [hsign, hpos, hab, hmul]
  let s : ℝ := Real.sqrt t
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = t := Real.sq_sqrt (by linarith)
  have hs1 : 1 < s :=
    (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hs0).mp
      (by simpa only [one_pow, hsq] using ht)
  have hcap0 : (q 0 : ℝ) + 3 ≤ (R : ℝ) ^ 2 := by
    have hh := hcap 0
    norm_num only [Nat.zero_add] at hh
    exact_mod_cast hh
  have hcap1 : (q 1 : ℝ) + 3 ≤ (R : ℝ) ^ 2 := by
    have hh := hcap 1
    norm_num only [Nat.zero_add] at hh
    exact_mod_cast hh
  have htR : t < (R : ℝ) ^ 2 := by linarith only [hsum, hcap0, hcap1]
  have hsR : s < (R : ℝ) :=
    (sq_lt_sq₀ hs0 (Nat.cast_nonneg R)).mp (by rw [hsq]; exact htR)
  have hspoly : s ^ 4 - ((q 0 : ℝ) + q 1 + 5) * s ^ 2 +
      ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2) = 0 := by
    calc
      _ = (s ^ 2 - (R : ℝ) ^ 2) * (s ^ 2 - t) := by rw [hsum, ← hprod]; ring
      _ = 0 := by rw [hsq]; ring
  have hsmem := (qadjacent_ordinary_spec_iff q hq2 hq3 s
    (by linarith) (by linarith) (by linarith)).mpr hspoly
  obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry (SG 4 (fun _ => 0) q) hG s hsmem
  have hz0 : (0 : ℤ) ≤ z := by rw [hz] at hs0; exact_mod_cast hs0
  have hn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hnR : (z.toNat : ℝ) = s := by
    have hh : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hn
    exact hh.trans hz.symm
  have hS1 : 1 < z.toNat := by
    have hh : (1 : ℝ) < (z.toNat : ℝ) := by rw [hnR]; exact hs1
    exact_mod_cast hh
  have hSR : z.toNat < R := by
    have hh : (z.toNat : ℝ) < R := by rw [hnR]; exact hsR
    exact_mod_cast hh
  refine ⟨R, z.toNat, hR, by omega, hSR, ?_, ?_⟩
  · have hh : (q 0 : ℝ) + q 1 + 5 = (R : ℝ) ^ 2 + (z.toNat : ℝ) ^ 2 := by
      rw [hnR, hsq]
      exact hsum
    exact_mod_cast hh
  · have hh : ((q 0 : ℝ) + 2) * ((q 1 : ℝ) + 2) =
        (R : ℝ) ^ 2 * (z.toNat : ℝ) ^ 2 := by rw [hnR, hsq]; exact hprod.symm
    exact_mod_cast hh
#print axioms Paper7B4Analytic.qadjacent_two_integer_roots

end Paper7B4Analytic
