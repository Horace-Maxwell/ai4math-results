import Research.Backfill.Paper7.C61ParameterMoments

set_option autoImplicit false
noncomputable section
namespace Paper7C61Parameters
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem support_sum (b : ℕ) (p : Fin b → ℕ) :
    (∑ k ∈ Kp b p, p k) = totalP b p := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _hk hn
  have hp : ¬ 0 < p k := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  omega
#print axioms Paper7C61Parameters.support_sum

theorem support_squares (b : ℕ) (p : Fin b → ℕ) :
    (∑ k ∈ Kp b p, p k ^ 2) = squares b p := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _hk hn
  have hp : p k = 0 := by
    have h : ¬ 0 < p k := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  simp only [hp, zero_pow (by decide : (2 : ℕ) ≠ 0)]
#print axioms Paper7C61Parameters.support_squares

theorem cauchy_on {b : ℕ} (S : Finset (Fin b)) (p : Fin b → ℕ) :
    (∑ k ∈ S, p k) ^ 2 ≤ S.card * ∑ k ∈ S, p k ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℕ)) p
#print axioms Paper7C61Parameters.cauchy_on

theorem support_cauchy (b : ℕ) (p : Fin b → ℕ) :
    totalP b p ^ 2 ≤ (Kp b p).card * squares b p := by
  have h := cauchy_on (Kp b p) p
  rwa [support_sum, support_squares] at h
#print axioms Paper7C61Parameters.support_cauchy

theorem load_squares_lower (b : ℕ) (p q : Fin b → ℕ) :
    squares b p + totalQ b q ≤ squares b (fun k => p k + q k) := by
  change (∑ k, p k ^ 2) + (∑ k, q k) ≤ ∑ k, (p k + q k) ^ 2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _hk
  nlinarith [Nat.le_mul_self (q k), Nat.zero_le (p k * q k)]
#print axioms Paper7C61Parameters.load_squares_lower

theorem zero_of_totalQ_zero (b : ℕ) (q : Fin b → ℕ) (hq : totalQ b q = 0) :
    q = (fun _ => 0) := by
  funext k
  have hk : q k ≤ totalQ b q :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ k)
  omega
#print axioms Paper7C61Parameters.zero_of_totalQ_zero

theorem squares_le_total_square (b : ℕ) (p : Fin b → ℕ) :
    squares b p ≤ totalP b p ^ 2 := by
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => Nat.zero_le (p k))
#print axioms Paper7C61Parameters.squares_le_total_square

theorem maximum_square_data (p : Fin 6 → ℕ) :
    ∃ M A B : ℕ, totalP 6 p = M + A ∧ squares 6 p = M ^ 2 + B ∧
      A ≤ B ∧ B ≤ A ^ 2 ∧ squares 6 p ≤ M * totalP 6 p := by
  obtain ⟨k, _hk, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6))
    p Finset.univ_nonempty
  let A : ℕ := ∑ j ∈ Finset.univ.erase k, p j
  let B : ℕ := ∑ j ∈ Finset.univ.erase k, p j ^ 2
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) p (Finset.mem_univ k)
  have hsq := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => p j ^ 2) (Finset.mem_univ k)
  have hAB : A ≤ B := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : p j = 0
    · simp [hj]
    · have hj1 : 1 ≤ p j := by omega
      nlinarith
  have hBA : B ≤ A ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => Nat.zero_le (p j))
  refine ⟨p k, A, B, ?_, ?_, hAB, hBA, ?_⟩
  · change (∑ j, p j) = p k + A
    change A + p k = ∑ j, p j at hsum
    omega
  · change (∑ j, p j ^ 2) = p k ^ 2 + B
    change B + p k ^ 2 = ∑ j, p j ^ 2 at hsq
    omega
  · change (∑ j, p j ^ 2) ≤ p k * ∑ j, p j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using Nat.mul_le_mul_right (p j) (hmax j hj)
#print axioms Paper7C61Parameters.maximum_square_data

theorem no_sum35_square1155 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 35) (hS : squares 6 p = 1155) : False := by
  obtain ⟨M, A, B, hMA, hMB, hAB, hBA, hmax⟩ := maximum_square_data p
  rw [hP] at hMA
  rw [hS] at hMB
  rw [hP, hS] at hmax
  by_cases hM : M ≤ 33
  · have hMeq : M = 33 := by omega
    have hAeq : A = 2 := by omega
    subst M
    subst A
    omega
  · have hM34 : 34 ≤ M := by omega
    have hp : 34 * M ≤ M ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right M hM34
    omega
#print axioms Paper7C61Parameters.no_sum35_square1155

theorem no_sum36_square1152 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 36) (hS : squares 6 p = 1152) : False := by
  obtain ⟨M, A, B, hMA, hMB, hAB, hBA, hmax⟩ := maximum_square_data p
  rw [hP] at hMA
  rw [hS] at hMB
  rw [hP, hS] at hmax
  by_cases hM : M ≤ 33
  · have hcases : M = 32 ∨ M = 33 := by omega
    rcases hcases with hMeq | hMeq
    · have hAeq : A = 4 := by omega
      subst M
      subst A
      omega
    · have hAeq : A = 3 := by omega
      subst M
      subst A
      omega
  · have hM34 : 34 ≤ M := by omega
    have hp : 34 * M ≤ M ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right M hM34
    omega
#print axioms Paper7C61Parameters.no_sum36_square1152

end Paper7C61Parameters
