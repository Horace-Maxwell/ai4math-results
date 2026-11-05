import Research.Backfill.Paper7.C61ProfileCore
import Research.Backfill.Paper7.IntegerSpectrum

/-! Complete integer-root products. The small factors 0,1,-1 are retained,
and the two large halves are paired only using actual even-graph symmetry. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Profile
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7OddIntegral
open scoped BigOperators Classical

theorem finite_count_prod {ι A M : Type*} [Fintype ι] [DecidableEq A]
    [CommMonoid M] (s : Multiset A) (e : ι → A) (he : Function.Injective e)
    (hcover : ∀ a ∈ s, ∃ i, e i = a) (f : A → M) :
    (s.map f).prod = ∏ i, f (e i) ^ s.count (e i) := by
  classical
  revert hcover
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons a s ih =>
    intro hcover
    obtain ⟨i, rfl⟩ := hcover a (Multiset.mem_cons_self a s)
    have hs : ∀ a ∈ s, ∃ j, e j = a :=
      fun a ha => hcover a (Multiset.mem_cons_of_mem ha)
    have hc (j : ι) : (e i ::ₘ s).count (e j) =
        s.count (e j) + if j = i then 1 else 0 := by
      by_cases h : j = i
      · subst j; simp
      · have hne : e j ≠ e i := fun hji => h (he hji)
        simp only [Multiset.count_cons_of_ne hne, ite_eq_right h, Nat.add_zero]
    have hd (j : ι) : f (e j) ^ (if j = i then 1 else 0 : ℕ) =
        if j = i then f (e j) else 1 := by
      by_cases h : j = i <;> simp [h]
    calc
      ((e i ::ₘ s).map f).prod = f (e i) * (s.map f).prod := by
        rw [Multiset.map_cons, Multiset.prod_cons]
      _ = (∏ j, f (e j) ^ s.count (e j)) * f (e i) := by
        rw [ih hs]; exact mul_comm _ _
      _ = ∏ j, f (e j) ^ (e i ::ₘ s).count (e j) := by
        simp_rw [hc, pow_add, hd]
        rw [Finset.prod_mul_distrib]
        simp
#print axioms Paper7C61Profile.finite_count_prod

theorem graphPhi_integer_root_product {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G) :
    graphPhi G = ((integerSpectrum G).map (fun z => X - C z)).prod := by
  obtain ⟨_S, hF⟩ := (Paper7Spectrum.integral_iff_integerFactorization G).mp hG
  have hs := (Paper7SpectralWindow.integerFactorizationOn_splits_roots hF).1
  have hroots : (graphPhi G).roots = integerSpectrum G := by
    apply Multiset.map_injective (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
    rw [integerSpectrum_cast G hG]
    change Multiset.map (Int.castRingHom ℝ) (graphPhi G).roots = spec G
    rw [← hs.roots_map_of_injective
      (i := Int.castRingHom ℝ) Int.cast_injective, Paper7Spectrum.graphPhi_map G ℝ]
    rfl
  rw [← hroots]
  exact hs.eq_prod_roots_of_monic (Matrix.charpoly_monic _)
#print axioms Paper7C61Profile.graphPhi_integer_root_product

theorem integer_product_partition (s : Multiset ℤ) :
    (s.map (fun z => (X - C z : Polynomial ℤ))).prod =
      X ^ s.count 0 * (X - 1) ^ s.count 1 * (X + 1) ^ s.count (-1) *
        ((s.filter (fun z => 2 ≤ z)).map (fun z => X - C z)).prod *
        (((s.map (fun z => -z)).filter (fun z => 2 ≤ z)).map
          (fun z => X + C z)).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    by_cases hp : 2 ≤ z
    · have hn : ¬ 2 ≤ -z := by omega
      have hz0 : z ≠ 0 := by omega
      have hz1 : z ≠ 1 := by omega
      have hzn1 : z ≠ -1 := by omega
      simp [hp, hn, Ne.symm hz0, Ne.symm hz1, Ne.symm hzn1]
      ring
    · by_cases hn : 2 ≤ -z
      · have hz0 : z ≠ 0 := by omega
        have hz1 : z ≠ 1 := by omega
        have hzn1 : z ≠ -1 := by omega
        simp [hp, hn, Ne.symm hz0, Ne.symm hz1, Ne.symm hzn1]
        ring
      · have hz : z = -1 ∨ z = 0 ∨ z = 1 := by omega
        rcases hz with rfl | rfl | rfl <;>
          norm_num [pow_succ] <;> ring
#print axioms Paper7C61Profile.integer_product_partition

theorem integerSpectrum_neg (p q : Fin 6 → ℕ) (hG : IsIntegralGraph (SG 6 p q)) :
    (integerSpectrum (SG 6 p q)).map (fun z => -z) = integerSpectrum (SG 6 p q) := by
  apply Multiset.ext.mpr
  intro z
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG (by decide)).1
  have hc := Multiset.count_map_eq_count' (fun z : ℤ => -z)
    (integerSpectrum (SG 6 p q)) neg_injective (-z)
  have hsym : (integerSpectrum (SG 6 p q)).count (-z) =
      (integerSpectrum (SG 6 p q)).count z := by
    rw [integerSpectrum_count _ hG, integerSpectrum_count _ hG]
    simpa only [Int.cast_neg, neg_neg] using hs (-(z : ℝ))
  simpa only [neg_neg] using hc.trans hsym
#print axioms Paper7C61Profile.integerSpectrum_neg

theorem integer_positive_prod (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (f : ℤ → Polynomial ℤ) :
    (((integerSpectrum (SG 6 p q)).filter (fun z => 2 ≤ z)).map f).prod =
      ∏ i : Fin 5, f (value i) ^ (actual p q i).val := by
  have hinj : Function.Injective (fun i : Fin 5 => (value i : ℤ)) := by
    intro i j hij
    apply value_injective
    change (value i : ℤ) = (value j : ℤ) at hij
    change (value i : ℝ) = (value j : ℝ)
    exact_mod_cast hij
  have hcover : ∀ z ∈ (integerSpectrum (SG 6 p q)).filter (fun z => 2 ≤ z),
      ∃ i : Fin 5, (value i : ℤ) = z := by
    intro z hz
    obtain ⟨hzs, hz2⟩ := Multiset.mem_filter.mp hz
    have hreal : (z : ℝ) ∈ spec (SG 6 p q) := by
      rw [← integerSpectrum_cast _ hG]
      exact Multiset.mem_map.mpr ⟨z, hzs, rfl⟩
    have h2 : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    have h6 := (le_abs_self (z : ℝ)).trans
      (Paper7C61Classification.spec_abs_le_six p q hn hG z hreal)
    obtain ⟨i, hi⟩ := value_rep z ⟨z, rfl⟩ h2 h6
    exact ⟨i, by exact_mod_cast hi⟩
  rw [finite_count_prod _ (fun i : Fin 5 => (value i : ℤ)) hinj hcover f]
  apply Finset.prod_congr rfl
  intro i _
  have h2 : (2 : ℤ) ≤ value i := by unfold value; omega
  have hc : ((integerSpectrum (SG 6 p q)).filter (fun z => 2 ≤ z)).count (value i : ℤ) =
      (actual p q i).val := by
    rw [Multiset.count_filter_of_pos h2, integerSpectrum_count _ hG, actual_eq_mult]
    norm_cast
  rw [hc]
#print axioms Paper7C61Profile.integer_positive_prod

def polynomial (m : Fin 5 → Fin 3) : Polynomial ℤ :=
  ∏ i, (X ^ 2 - C ((value i : ℤ) ^ 2)) ^ (m i).val
#print axioms Paper7C61Profile.polynomial

theorem graphPhi_profile (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    graphPhi (SG 6 p q) = X ^ mult (SG 6 p q) 0 *
      (X ^ 2 - 1) ^ mult (SG 6 p q) 1 * polynomial (actual p q) := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG (by decide)).1
  rw [graphPhi_integer_root_product _ hG, integer_product_partition, integerSpectrum_neg p q hG,
    integer_positive_prod p q hn hG, integer_positive_prod p q hn hG]
  have hc0 : (integerSpectrum (SG 6 p q)).count 0 = mult (SG 6 p q) 0 := by
    simpa using integerSpectrum_count (SG 6 p q) hG 0
  have hc1 : (integerSpectrum (SG 6 p q)).count 1 = mult (SG 6 p q) 1 := by
    simpa using integerSpectrum_count (SG 6 p q) hG 1
  have hcn : (integerSpectrum (SG 6 p q)).count (-1) = mult (SG 6 p q) 1 := by
    have hc : (integerSpectrum (SG 6 p q)).count (-1) = mult (SG 6 p q) (-1) := by
      simpa using integerSpectrum_count (SG 6 p q) hG (-1)
    exact hc.trans (hs 1).symm
  rw [hc0, hc1, hcn]
  have hunit : (X - 1 : Polynomial ℤ) * (X + 1) = X ^ 2 - 1 := by ring
  have hlarge :
      (∏ i : Fin 5, (X - C (value i : ℤ)) ^ (actual p q i).val) *
      (∏ i : Fin 5, (X + C (value i : ℤ)) ^ (actual p q i).val) =
        polynomial (actual p q) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow]
    congr 1
    rw [map_pow]
    ring
  calc
    _ = X ^ mult (SG 6 p q) 0 *
        ((X - 1) ^ mult (SG 6 p q) 1 * (X + 1) ^ mult (SG 6 p q) 1) *
        ((∏ i : Fin 5, (X - C (value i : ℤ)) ^ (actual p q i).val) *
          (∏ i : Fin 5, (X + C (value i : ℤ)) ^ (actual p q i).val)) := by ring
    _ = _ := by rw [← mul_pow, hunit, hlarge]
#print axioms Paper7C61Profile.graphPhi_profile

end Paper7C61Profile
