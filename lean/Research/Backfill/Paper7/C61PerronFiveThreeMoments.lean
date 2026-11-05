import Research.Backfill.Paper7.C61SparseProfileExclusion

/-! Source-only exact moment obstructions for the remaining {2,3,5} branch.
No coordinate enumeration or finite candidate table is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61FiveThree
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61Sparse Paper7C61ThreeSquareObstruction
open scoped BigOperators Classical

theorem erase_coordinate_moments (p : Fin 6 → ℕ) (k : Fin 6) :
    ∃ r : Fin 6 → ℕ,
      totalP 6 r + p k = totalP 6 p ∧
      squares 6 r + p k ^ 2 = squares 6 p := by
  let r : Fin 6 → ℕ := fun j => if j = k then 0 else p j
  have hrk : r k = 0 := by simp [r]
  have hr (j : Fin 6) (hj : j ∈ Finset.univ.erase k) : r j = p j := by
    simp only [r, ite_eq_right (Finset.mem_erase.mp hj).1]
  have hP := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) p (Finset.mem_univ k)
  have hS := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => p j ^ 2) (Finset.mem_univ k)
  have hrP := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) r (Finset.mem_univ k)
  have hrS := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => r j ^ 2) (Finset.mem_univ k)
  have hPeq : (∑ j ∈ Finset.univ.erase k, r j) = ∑ j ∈ Finset.univ.erase k, p j :=
    Finset.sum_congr rfl hr
  have hSeq : (∑ j ∈ Finset.univ.erase k, r j ^ 2) =
      ∑ j ∈ Finset.univ.erase k, p j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hr j hj]
  change (∑ j ∈ Finset.univ.erase k, p j) + p k = totalP 6 p at hP
  change (∑ j ∈ Finset.univ.erase k, p j ^ 2) + p k ^ 2 = squares 6 p at hS
  change (∑ j ∈ Finset.univ.erase k, r j) + r k = totalP 6 r at hrP
  change (∑ j ∈ Finset.univ.erase k, r j ^ 2) + r k ^ 2 = squares 6 r at hrS
  rw [hPeq, hrk] at hrP
  rw [hSeq, hrk] at hrS
  norm_num at hrP hrS
  exact ⟨r, by omega, by omega⟩
#print axioms Paper7C61FiveThree.erase_coordinate_moments

theorem no_sum12_square132 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 12) (hS : squares 6 p = 132) : False := by
  obtain ⟨M,h0,_hMP,hm,hl,hu⟩ := maximum_moment_interval p 12 132 hP hS
  norm_num at hm hl hu
  have hlo : 11 ≤ M := by omega
  have hhi : M ≤ 11 := by
    by_contra h
    have h12 : 12 ≤ M := by omega
    have hp := mul_nonneg (sub_nonneg.mpr h12) h0
    nlinarith
  have heq : M = 11 := by omega
  rw [heq] at hu
  norm_num at hu
#print axioms Paper7C61FiveThree.no_sum12_square132

theorem no_sum11_square89 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 11) (hS : squares 6 p = 89) : False := by
  obtain ⟨M,h0,_hMP,hm,hl,hu⟩ := maximum_moment_interval p 11 89 hP hS
  norm_num at hm hl hu
  have hlo : 9 ≤ M := by omega
  have hhi : M ≤ 9 := by
    by_contra h
    have h10 : 10 ≤ M := by omega
    have hp := mul_nonneg (sub_nonneg.mpr h10) h0
    nlinarith
  have heq : M = 9 := by omega
  rw [heq] at hu
  norm_num at hu
#print axioms Paper7C61FiveThree.no_sum11_square89

theorem cap22_sum33_square573_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 33) (hS : squares 6 p = 573)
    (hcap : ∀ k, p k ≤ 22) : False := by
  obtain ⟨k,_hk,hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 6)) p Finset.univ_nonempty
  obtain ⟨r,hrP,hrS⟩ := erase_coordinate_moments p k
  rw [hP] at hrP
  rw [hS] at hrS
  have hm : squares 6 p ≤ p k * totalP 6 p := by
    change (∑ j, p j ^ 2) ≤ p k * ∑ j, p j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using Nat.mul_le_mul_right (p j) (hmax j hj)
  rw [hP,hS] at hm
  have hlo : 18 ≤ p k := by omega
  have hhi := hcap k
  have hu := squares_le_total_square 6 r
  have hrPZ : (totalP 6 r : ℤ) + (p k : ℤ) = 33 := by exact_mod_cast hrP
  have hrSZ : (squares 6 r : ℤ) + (p k : ℤ) ^ 2 = 573 := by exact_mod_cast hrS
  have huZ : (squares 6 r : ℤ) ≤ (totalP 6 r : ℤ) ^ 2 := by exact_mod_cast hu
  have hrem : (totalP 6 r : ℤ) = 33 - (p k : ℤ) := by omega
  rw [hrem] at huZ
  have hk21 : 21 ≤ p k := by
    by_contra h
    have hk20 : (p k : ℤ) ≤ 20 := by exact_mod_cast (by omega : p k ≤ 20)
    have hk18 : (18 : ℤ) ≤ p k := by exact_mod_cast hlo
    have hp := mul_nonneg (sub_nonneg.mpr hk18) (sub_nonneg.mpr hk20)
    nlinarith
  have hcases : p k = 21 ∨ p k = 22 := by omega
  rcases hcases with hk | hk
  · rw [hk] at hrP hrS
    norm_num at hrS
    exact no_sum12_square132 r (by omega) (by omega)
  · rw [hk] at hrP hrS
    norm_num at hrS
    exact no_sum11_square89 r (by omega) (by omega)
#print axioms Paper7C61FiveThree.cap22_sum33_square573_impossible

end Paper7C61FiveThree
