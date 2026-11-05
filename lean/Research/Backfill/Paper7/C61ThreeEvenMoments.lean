import Research.Backfill.Paper7.C61ThreeMonodromy
import Research.Backfill.Paper7.C61FourSquareObstruction
import Research.Backfill.Paper7.C61SparseSupportRepresentation

/-! Analytic obstruction for the original beta-seven zero-q domain.
All support coordinates are retained; no tuple certificate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters Paper7C61Sparse Paper7C61BetaEight
open scoped BigOperators Classical Matrix

theorem support_four_square_multiple_eight_even (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4) (hS : 8 ∣ squares 6 p) : ∀ t, 2 ∣ p t := by
  obtain ⟨S,hKS,_hSU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Kp 6 p)) hK
    (by simp : 4 ≤ (Finset.univ : Finset (Fin 6)).card)
  obtain ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,hset⟩ := Finset.card_eq_four.mp hcard
  have hsq := (moments_on_support_superset p S hKS).2
  rw [hset] at hsq
  simp [hij,hik,hil,hjk,hjl,hkl] at hsq
  have hsqZ : (p i : ℤ)^2+(p j : ℤ)^2+(p k : ℤ)^2+(p l : ℤ)^2 =
      (squares 6 p : ℤ) := by
    exact_mod_cast (by omega : p i^2+p j^2+p k^2+p l^2 = squares 6 p)
  have h8 : (8 : ℤ) ∣ (p i : ℤ)^2+(p j : ℤ)^2+(p k : ℤ)^2+(p l : ℤ)^2 := by
    rw [hsqZ]
    exact_mod_cast hS
  obtain ⟨hi,hj,hk,hl⟩ := four_squares_eight_divides_even _ _ _ _ h8
  intro t
  by_cases ht : t ∈ S
  · rw [hset] at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact_mod_cast hi
    · exact_mod_cast hj
    · exact_mod_cast hk
    · exact_mod_cast hl
  · have hz : p t = 0 := by
      by_contra h
      exact ht (hKS (Finset.mem_filter.mpr ⟨Finset.mem_univ t,by omega⟩))
    rw [hz]
    exact dvd_zero 2
#print axioms Paper7C61Three.support_four_square_multiple_eight_even

theorem equal_sums_pointwise (f g : Fin 6 → ℕ) (hle : ∀ i, f i ≤ g i)
    (hs : (∑ i, f i) = ∑ i, g i) : ∀ i, f i = g i := by
  intro i
  have hf := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) f (Finset.mem_univ i)
  have hg := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) g (Finset.mem_univ i)
  have hr : (∑ j ∈ Finset.univ.erase i, f j) ≤ ∑ j ∈ Finset.univ.erase i, g j :=
    Finset.sum_le_sum (fun j _ => hle j)
  have hi := hle i
  omega
#print axioms Paper7C61Three.equal_sums_pointwise

theorem minus_one_head_impossible (b c d e f : ℤ)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : d ≤ 2) (he : 1 ≤ e) (hf : 1 ≤ f)
    (h : sixProduct (-1) b c d e f = 1) : False := by
  obtain ⟨h01,h12,_hpoly⟩ := six_product_triple_data (-1) b c d e f h
  have hbc : 1 ≤ b*c := by nlinarith [mul_nonneg (show 0 ≤ b-1 by omega) (show 0 ≤ c-1 by omega)]
  have hef : 1 ≤ e*f := by nlinarith [mul_nonneg (show 0 ≤ e-1 by omega) (show 0 ≤ f-1 by omega)]
  have hbmul : b ≤ b*c := by nlinarith [mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ c-1 by omega)]
  have hemul : e ≤ e*f := by nlinarith [mul_nonneg (show 0 ≤ e by omega) (show 0 ≤ f-1 by omega)]
  have hb1 : b = 1 := by omega
  have he1 : e = 1 := by omega
  rw [hb1,he1] at h01
  omega
#print axioms Paper7C61Three.minus_one_head_impossible

theorem sum_six_square_twelve_no_identity (r : Fin 6 → ℕ)
    (hcap : ∀ i, r i ≤ 3) (hs : totalP 6 r = 6) (hq : squares 6 r = 12)
    (hm : sixProduct (2-(r 0 : ℤ)) (2-(r 1 : ℤ)) (2-(r 2 : ℤ))
      (2-(r 3 : ℤ)) (2-(r 4 : ℤ)) (2-(r 5 : ℤ)) = 1) : False := by
  by_cases hsmall : ∀ i, r i ≤ 2
  · have hle (i : Fin 6) : r i^2 ≤ 2*r i := by
      nlinarith [hsmall i]
    have heq : ∀ i, r i^2 = 2*r i := equal_sums_pointwise _ _ hle (by
      change squares 6 r = ∑ i, 2*r i
      rw [← Finset.mul_sum]
      change squares 6 r = 2*totalP 6 r
      rw [hs,hq])
    have heven (i : Fin 6) : (2 : ℤ) ∣ 2-(r i : ℤ) := by
      have hi := heq i
      have hiZ : (r i : ℤ)^2 = 2*(r i : ℤ) := by exact_mod_cast hi
      have hzero : (r i : ℤ)*((r i : ℤ)-2) = 0 := by nlinarith only [hiZ]
      rcases mul_eq_zero.mp hzero with h0 | h2
      · rw [h0]; norm_num
      · have hr2 : (r i : ℤ) = 2 := by omega
        rw [hr2]; norm_num
    have hpair := (six_product_triple_data _ _ _ _ _ _ hm).1
    have hd : (4 : ℤ) ∣ (2-(r 0 : ℤ))*(2-(r 1 : ℤ))+
        (2-(r 3 : ℤ))*(2-(r 4 : ℤ)) :=
      dvd_add (mul_dvd_mul (heven 0) (heven 1)) (mul_dvd_mul (heven 3) (heven 4))
    rw [hpair] at hd
    norm_num at hd
  · push Not at hsmall
    obtain ⟨k,hk⟩ := hsmall
    have hk3 : r k = 3 := by have h := hcap k; omega
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) r (Finset.mem_univ k)
    have hsquare := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
      (fun i => r i^2) (Finset.mem_univ k)
    change (∑ i ∈ Finset.univ.erase k, r i)+r k = totalP 6 r at hsum
    change (∑ i ∈ Finset.univ.erase k, r i^2)+r k^2 = squares 6 r at hsquare
    have hrest (i : Fin 6) (hik : i ≠ k) : r i ≤ 1 := by
      have hrem : (∑ j ∈ (Finset.univ.erase k).erase i, r j) ≤
          ∑ j ∈ (Finset.univ.erase k).erase i, r j^2 := by
        apply Finset.sum_le_sum
        intro j _hj
        by_cases hz : r j = 0
        · simp [hz]
        · have hp : 1 ≤ r j := by omega
          nlinarith
      have hi : i ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩
      have hs' := Finset.sum_erase_add (Finset.univ.erase k) r hi
      have hq' := Finset.sum_erase_add (Finset.univ.erase k) (fun j => r j^2) hi
      rw [hk3,hs] at hsum
      rw [hk3,hq] at hsquare
      have hineq : r i^2 ≤ r i := by omega
      nlinarith
    have hm1 := six_product_rotate _ _ _ _ _ _ hm
    have hm2 := six_product_rotate _ _ _ _ _ _ hm1
    have hm3 := six_product_rotate _ _ _ _ _ _ hm2
    have hm4 := six_product_rotate _ _ _ _ _ _ hm3
    have hm5 := six_product_rotate _ _ _ _ _ _ hm4
    have hbound (i : Fin 6) (hik : i ≠ k) :
        1 ≤ 2-(r i : ℤ) ∧ 2-(r i : ℤ) ≤ 2 := by
      have hi := hrest i hik
      omega
    fin_cases k
    · change r (0 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm
      exact minus_one_head_impossible _ _ _ _ _ (hbound 1 (by decide)).1
        (hbound 2 (by decide)).1 (hbound 3 (by decide)).2
        (hbound 4 (by decide)).1 (hbound 5 (by decide)).1 hm
    · change r (1 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm1
      exact minus_one_head_impossible _ _ _ _ _ (hbound 2 (by decide)).1
        (hbound 3 (by decide)).1 (hbound 4 (by decide)).2
        (hbound 5 (by decide)).1 (hbound 0 (by decide)).1 hm1
    · change r (2 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm2
      exact minus_one_head_impossible _ _ _ _ _ (hbound 3 (by decide)).1
        (hbound 4 (by decide)).1 (hbound 5 (by decide)).2
        (hbound 0 (by decide)).1 (hbound 1 (by decide)).1 hm2
    · change r (3 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm3
      exact minus_one_head_impossible _ _ _ _ _ (hbound 4 (by decide)).1
        (hbound 5 (by decide)).1 (hbound 0 (by decide)).2
        (hbound 1 (by decide)).1 (hbound 2 (by decide)).1 hm3
    · change r (4 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm4
      exact minus_one_head_impossible _ _ _ _ _ (hbound 5 (by decide)).1
        (hbound 0 (by decide)).1 (hbound 1 (by decide)).2
        (hbound 2 (by decide)).1 (hbound 3 (by decide)).1 hm4
    · change r (5 : Fin 6) = 3 at hk3
      norm_num [hk3] at hm5
      exact minus_one_head_impossible _ _ _ _ _ (hbound 0 (by decide)).1
        (hbound 1 (by decide)).1 (hbound 2 (by decide)).2
        (hbound 3 (by decide)).1 (hbound 4 (by decide)).1 hm5
#print axioms Paper7C61Three.sum_six_square_twelve_no_identity

end Paper7C61Three
