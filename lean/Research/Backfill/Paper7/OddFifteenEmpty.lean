import Research.Backfill.Paper7.OddAdmissibleCongruence
import Research.Backfill.Paper7.OddMomentVandermonde

/-! Source-only obstruction for b=15. Six zero odd moments force the entire
nonzero signed support to vanish, contradicting the actual Perron count. -/
set_option autoImplicit false
noncomputable section
namespace Paper7FeatureEmpty
open Finset BackfillPaper7.Challenge.Legacy

def signedSupport (s : SpectralCounts) : Finset (Fin 8) :=
  univ.filter (fun i => (s.1 i).val ≠ (s.2 i).val)
#print axioms Paper7FeatureEmpty.signedSupport

theorem signed_support_point_bound (s : SpectralCounts) (i : Fin 8) :
    (16 : ℤ) * (if i ∈ signedSupport s then 1 else 0) ≤
      (((s.1 i).val + (s.2 i).val : ℕ) : ℤ) * (value i : ℤ)^2 +
        (if i = 0 then 12 else 0) + (if i = 1 then 7 else 0) := by
  by_cases hi : i ∈ signedSupport s
  · have hne : (s.1 i).val ≠ (s.2 i).val := (mem_filter.mp hi).2
    have hsumN : 1 ≤ (s.1 i).val + (s.2 i).val := by omega
    have hsum : (1 : ℤ) ≤ ((s.1 i).val + (s.2 i).val : ℕ) := by exact_mod_cast hsumN
    rw [ite_eq_left hi, mul_one]
    by_cases h0 : i = 0
    · subst i
      norm_num [value]
      omega
    · by_cases h1 : i = 1
      · subst i
        norm_num [value]
        omega
      · have hi0 : i.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hi1 : i.val ≠ 1 := by intro h; exact h1 (Fin.ext h)
        have hvN : 4 ≤ value i := by unfold value; omega
        have hv : (4 : ℤ) ≤ value i := by exact_mod_cast hvN
        have hv2 : (16 : ℤ) ≤ (value i : ℤ)^2 := by nlinarith
        simp only [ite_eq_right h0, ite_eq_right h1, add_zero]
        calc
          (16 : ℤ) = 1 * 16 := by norm_num
          _ ≤ (((s.1 i).val + (s.2 i).val : ℕ) : ℤ) * (value i : ℤ)^2 :=
            mul_le_mul hsum hv2 (by norm_num) (by positivity)
  · rw [ite_eq_right hi, mul_zero]
    positivity
#print axioms Paper7FeatureEmpty.signed_support_point_bound

theorem odd_signed_support_budget (b : ℕ) (s : SpectralCounts) (ho : Odd b) :
    16 * ((signedSupport s).card : ℤ) ≤ s2 b s + 19 := by
  have hn : ¬ Even b := Nat.not_even_iff_odd.mpr ho
  calc
    16 * ((signedSupport s).card : ℤ) =
        ∑ i : Fin 8, (16 : ℤ) * (if i ∈ signedSupport s then 1 else 0) := by
      rw [← mul_sum]
      congr 1
      simp
    _ ≤ ∑ i : Fin 8, ((((s.1 i).val + (s.2 i).val : ℕ) : ℤ) * (value i : ℤ)^2 +
        (if i = 0 then 12 else 0) + (if i = 1 then 7 else 0)) :=
      sum_le_sum (fun i _ => signed_support_point_bound s i)
    _ = s2 b s + 19 := by
      simp [s2, hn, sum_add_distrib, add_assoc]
#print axioms Paper7FeatureEmpty.odd_signed_support_budget

theorem admissible_fifteen_support_le_six (cyc : Bool) (N : ℕ) (hN : N ≤ 42)
    (s : SpectralCounts) (hs : Admissible cyc 15 N s) : (signedSupport s).card ≤ 6 := by
  have hbudget := odd_signed_support_budget 15 s (by decide)
  have hupper : s2 15 s ≤ 2 * N := by
    simpa only [ite_eq_right (by decide : ¬ Even 15)] using hs.1.2.1
  have hNint : (N : ℤ) ≤ 42 := by exact_mod_cast hN
  omega
#print axioms Paper7FeatureEmpty.admissible_fifteen_support_le_six

theorem admissible_fifteen_false (cyc : Bool) (N : ℕ) (hN : N ≤ 42)
    (s : SpectralCounts) : ¬ Admissible cyc 15 N s := by
  classical
  intro hs
  let I := signedSupport s
  let w : I → ℝ := fun i => (value i.val : ℝ)^2
  let c : I → ℝ := fun i =>
    (((s.1 i.val).val : ℝ) - (s.2 i.val).val) * (value i.val : ℝ)
  have hcard : I.card ≤ 6 := admissible_fifteen_support_le_six cyc N hN s hs
  have hvalue (i : Fin 8) : (2 : ℝ) ≤ (value i : ℝ) := by
    have h : (2 : ℕ) ≤ value i := by unfold value; omega
    exact_mod_cast h
  have hw : Function.Injective w := by
    intro i j hij
    have he : (value i.val : ℝ) = (value j.val : ℝ) :=
      (sq_eq_sq₀ (by linarith [hvalue i.val]) (by linarith [hvalue j.val])).mp hij
    have heN : value i.val = value j.val := by exact_mod_cast he
    apply Subtype.ext
    apply Fin.ext
    unfold value at heN
    omega
  have h1 : ∀ i, w i ≠ 1 := by
    intro i hi
    change (value i.val : ℝ)^2 = 1 at hi
    nlinarith [hvalue i.val]
  have hm : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card I →
      ∑ i : I, c i * (w i ^ j - 1) = 0 := by
    intro j hj hji
    have hj6 : j ≤ 6 := by
      have h' : j ≤ I.card := by simpa only [Fintype.card_coe] using hji
      omega
    have hLodd : Odd (2*j+1) := ⟨j, by omega⟩
    have hL3 : 3 ≤ 2*j+1 := by omega
    have hL15 : 2*j+1 < 15 := by omega
    have hz := hs.1.2.2 (by decide : Odd 15) (2*j+1) hLodd hL3 hL15.le
    rw [ite_eq_right (by omega : 2*j+1 ≠ 15)] at hz
    have hr : (∑ i : Fin 8, (((s.1 i).val : ℝ) - (s.2 i).val) *
        ((value i : ℝ)^(2*j+1)-value i)) = 0 := by exact_mod_cast hz
    have hrestrict : (∑ i : I, (((s.1 i.val).val : ℝ) - (s.2 i.val).val) *
        ((value i.val : ℝ)^(2*j+1)-value i.val)) =
        ∑ i : Fin 8, (((s.1 i).val : ℝ) - (s.2 i).val) *
          ((value i : ℝ)^(2*j+1)-value i) := by
      rw [Finset.sum_coe_sort I (fun i : Fin 8 =>
        (((s.1 i).val : ℝ) - (s.2 i).val) *
          ((value i : ℝ) ^ (2*j+1) - value i))]
      change (∑ i ∈ univ.filter (fun i : Fin 8 => (s.1 i).val ≠ (s.2 i).val),
        (((s.1 i).val : ℝ)-(s.2 i).val) * ((value i : ℝ)^(2*j+1)-value i)) = _
      rw [Finset.sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases hi : (s.1 i).val = (s.2 i).val <;> simp [hi]
    calc
      _ = ∑ i : I, (((s.1 i.val).val : ℝ) - (s.2 i.val).val) *
          ((value i.val : ℝ)^(2*j+1)-value i.val) := by
        apply sum_congr rfl
        intro i _
        simp only [c, w, pow_add, pow_mul, pow_one]
        ring
      _ = 0 := hrestrict.trans hr
  have hc : c = 0 := Paper7OddIntegral.shifted_moments_force_zero w c hw h1 hm
  obtain ⟨ρ, _hρ3, hp, _htop, hn⟩ := hs.1.1
  rw [ite_eq_right (by decide : ¬ Even 15)] at hn
  have hneg := hn ρ (le_refl _)
  have hpv : (s.1 ρ).val = 1 := congrArg Fin.val hp
  have hnv : (s.2 ρ).val = 0 := congrArg Fin.val hneg
  have hρI : ρ ∈ I := by
    apply mem_filter.mpr
    exact ⟨mem_univ _, by omega⟩
  have he := congrFun hc ⟨ρ, hρI⟩
  change (((s.1 ρ).val : ℝ) - (s.2 ρ).val) * (value ρ : ℝ) = 0 at he
  rw [hpv, hnv] at he
  norm_num at he
  linarith [hvalue ρ]
#print axioms Paper7FeatureEmpty.admissible_fifteen_false

theorem fifteen_odd_cell_empty (cyc : Bool) (N : ℕ) (hN : N ≤ 42) :
    {s | Admissible cyc 15 N s} = ∅ := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact admissible_fifteen_false cyc N hN s
#print axioms Paper7FeatureEmpty.fifteen_odd_cell_empty

end Paper7FeatureEmpty
