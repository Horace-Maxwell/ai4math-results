import Research.TaskU.H5.TraceCongruence
import Research.TaskU.H5.TraceProfile
import Research.TaskU.H5.CycNorm
import Mathlib.Algebra.Field.ZMod

namespace TaskU.H5.TraceWords
noncomputable section
open Finset
local instance traceIntegralPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private def joint (f : H → ℤ) (b e : K) : ℤ :=
  ∑ q : Word, if mass q=b ∧ phase q=e then weight f q else 0

private theorem joint_translate (f : H → ℤ) (e : K) {b : K} (hb : b ≠ 0) :
    joint f b e = joint f b 4 := by
  let t := (4-e)/b
  let val (q : Word) := if mass q=b ∧ phase q=e then weight f q else 0
  have hs : ∑ q : Word, val (translate t q) = ∑ q : Word, val q := Equiv.sum_comp (spin t) val
  change ∑ q : Word, val q = _
  rw [← hs]
  unfold joint
  apply sum_congr rfl
  intro q _
  by_cases h : mass q=b
  · have ht : t*b = 4-e := div_mul_cancel₀ _ hb
    have he : phase q-(4-e)=e ↔ phase q=4 := by
      constructor <;> intro h' <;> linear_combination h'
    simp [val, mass_translate, phase_translate, weight_translate, h, ht, he]
  · simp [val, mass_translate, h]

private theorem sum_joint (f : H → ℤ) (e : K) :
    ∑ b : K, joint f b e = counts (weight f) phase e := by
  unfold joint counts
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases h : phase q=e <;> simp [h]

private theorem diff_count (f : H → ℤ) (e : K) :
    counts (weight f) phase e - counts (weight f) phase 4 = binWeight f e - binWeight f 4 := by
  rw [← sum_joint, ← sum_joint, ← sum_sub_distrib]
  rw [← Finset.add_sum_erase _ _ (mem_univ (0:K))]
  have vanish : ∑ b ∈ (univ : Finset K).erase 0, (joint f b e - joint f b 4) = 0 := by
    apply sum_eq_zero
    intro b hb
    rw [joint_translate f e (ne_of_mem_erase hb), sub_self]
  rw [vanish, add_zero]
  rfl

private theorem sum_bin (f : H → ℤ) : ∑ e : K, binWeight f e = integerAverage f := by
  unfold binWeight integerAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases h : mass q=0 <;> simp [h]

theorem integral_congruence (f : H → ℤ) :
    ∃ u : Cyc5.V, nonlinear f = Cyc5.add (Cyc5.scalar (integerAverage f)) (Cyc5.mul (Cyc5.scalar 5) u) ∧
      5 ∣ Cyc5.sumCoeff u := by
  let A := anchoredWeight f
  refine ⟨⟨-A 1-A 2-A 3-2*A 4, A 1-A 4, A 2-A 4, A 3-A 4⟩, ?_, ?_⟩
  · have hs := sum_bin f
    rw [sum_five] at hs
    have h1 := binWeight_eq_five f (by decide : (1:K) ≠ 0)
    have h2 := binWeight_eq_five f (by decide : (2:K) ≠ 0)
    have h3 := binWeight_eq_five f (by decide : (3:K) ≠ 0)
    have h4 := binWeight_eq_five f (by decide : (4:K) ≠ 0)
    ext <;> simp only [nonlinear, profile, diff_count, Cyc5.add, Cyc5.scalar, Cyc5.mul,
      zero_mul, zero_add, add_zero, sub_zero, A] <;> omega
  · refine ⟨-A 4, ?_⟩
    simp [Cyc5.sumCoeff]
    ring

theorem average_dvd_iff_profile (f : H → ℤ) :
    5 ∣ integerAverage f ↔ 5 ∣ Cyc5.sumCoeff (nonlinear f) := by
  obtain ⟨u,h,_⟩ := integral_congruence f
  rw [h]
  simp [Cyc5.sumCoeff, Cyc5.add, Cyc5.scalar, Cyc5.mul]

theorem norm_divisibility (f : H → ℤ) (h : 5 ∣ integerAverage f) :
    625 ∣ Cyc5.norm (nonlinear f) := by
  obtain ⟨u,hu,_⟩ := integral_congruence f
  obtain ⟨k,hk⟩ := h
  have he : nonlinear f = Cyc5.mul (Cyc5.scalar 5) (Cyc5.add (Cyc5.scalar k) u) := by
    rw [hu,hk]
    ext <;> simp [Cyc5.add,Cyc5.scalar,Cyc5.mul]
    all_goals ring
  rw [he,Cyc5.norm_mul,show Cyc5.norm (Cyc5.scalar 5)=625 by decide]
  exact dvd_mul_right .. 

theorem norm_deep (f : H → ℤ) (h : 25 ∣ integerAverage f) :
    3125 ∣ Cyc5.norm (nonlinear f) := by
  obtain ⟨u,hu,hd⟩ := integral_congruence f
  obtain ⟨k,hk⟩ := h
  let z := Cyc5.add (Cyc5.scalar (5*k)) u
  have he : nonlinear f = Cyc5.mul (Cyc5.scalar 5) z := by
    rw [hu,hk]
    ext <;> simp [z,Cyc5.add,Cyc5.scalar,Cyc5.mul]
    all_goals ring
  have hm : 5 ∣ Cyc5.norm z := by
    rw [Cyc5.five_dvd_norm_iff]
    simp [z,Cyc5.sumCoeff,Cyc5.add,Cyc5.scalar] at hd ⊢
    omega
  obtain ⟨j,hj⟩ := hm
  refine ⟨j,?_⟩
  rw [he,Cyc5.norm_mul,hj,show Cyc5.norm (Cyc5.scalar 5)=625 by decide]
  ring
end
end TaskU.H5.TraceWords
