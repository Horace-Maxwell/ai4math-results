import Research.Backfill.Paper7.C61PerronDegreeBound

set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters
open scoped BigOperators Classical

/-- The maximum is chosen from the actual six coordinates, so a pointwise
Perron cap bounds the same maximum used in the moment estimate. -/
theorem capped_maximum_moment (p : Fin 6 → ℕ) (P S B : ℕ)
    (hP : totalP 6 p = P) (hS : squares 6 p = S) (hcap : ∀ k, p k ≤ B) :
    ∃ M : ℤ, 0 ≤ M ∧ M ≤ B ∧ (S : ℤ) ≤ M*P ∧
      (S : ℤ) ≤ M^2+((P : ℤ)-M)^2 := by
  obtain ⟨k,_hk,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6)) p Finset.univ_nonempty
  let A : ℕ := ∑ j ∈ Finset.univ.erase k, p j
  let T : ℕ := ∑ j ∈ Finset.univ.erase k, p j^2
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) p (Finset.mem_univ k)
  have hsq := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) (fun j => p j^2) (Finset.mem_univ k)
  change A+p k = totalP 6 p at hsum
  change T+p k^2 = squares 6 p at hsq
  rw [hP] at hsum
  rw [hS] at hsq
  have hTA : T ≤ A^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => Nat.zero_le (p j))
  have hsumZ : (A : ℤ)+(p k : ℤ) = P := by exact_mod_cast hsum
  have hsqZ : (T : ℤ)+(p k : ℤ)^2 = S := by exact_mod_cast hsq
  have hTAZ : (T : ℤ) ≤ (A : ℤ)^2 := by exact_mod_cast hTA
  have hAZ : (A : ℤ) = (P : ℤ)-(p k : ℤ) := by omega
  rw [hAZ] at hTAZ
  have hm : squares 6 p ≤ p k*totalP 6 p := by
    change (∑ j, p j^2) ≤ p k*∑ j, p j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using Nat.mul_le_mul_right (p j) (hmax j hj)
  rw [hP,hS] at hm
  exact ⟨p k,Int.natCast_nonneg _,by exact_mod_cast hcap k,by exact_mod_cast hm,by omega⟩
#print axioms Paper7C61Higher.capped_maximum_moment

theorem cap13_sum20_square240_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 20) (hS : squares 6 p = 240) (hc : ∀ k,p k ≤ 13) : False := by
  obtain ⟨M,_h0,hhi,hm,hs⟩ := capped_maximum_moment p 20 240 13 hP hS hc
  norm_num at hhi hm hs
  have hlo : 12 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap13_sum20_square240_impossible

theorem cap13_sum21_square237_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 21) (hS : squares 6 p = 237) (hc : ∀ k,p k ≤ 13) : False := by
  obtain ⟨M,_h0,hhi,hm,hs⟩ := capped_maximum_moment p 21 237 13 hP hS hc
  norm_num at hhi hm hs
  have hlo : 12 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap13_sum21_square237_impossible

theorem cap22_sum29_square573_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 29) (hS : squares 6 p = 573) (hc : ∀ k,p k ≤ 22) : False := by
  obtain ⟨M,_h0,hhi,hm,hs⟩ := capped_maximum_moment p 29 573 22 hP hS hc
  norm_num at hhi hm hs
  have hlo : 20 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum29_square573_impossible

theorem cap22_sum30_square570_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 30) (hS : squares 6 p = 570) (hc : ∀ k,p k ≤ 22) : False := by
  obtain ⟨M,_h0,hhi,hm,hs⟩ := capped_maximum_moment p 30 570 22 hP hS hc
  norm_num at hhi hm hs
  have hlo : 19 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum30_square570_impossible

theorem cap22_sum36_square720_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 36) (hS : squares 6 p = 720) (hc : ∀ k,p k ≤ 22) : False := by
  obtain ⟨M,_h0,hhi,hm,hs⟩ := capped_maximum_moment p 36 720 22 hP hS hc
  norm_num at hhi hm hs
  have hlo : 20 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum36_square720_impossible

end Paper7C61Higher
