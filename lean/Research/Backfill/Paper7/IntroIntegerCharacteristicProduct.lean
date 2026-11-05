import Research.Backfill.Paper7.IntroIntegerWindowCounts

/-! Actual integer-spectrum factorization. The finite support used below is
proved from the original graph hypotheses, rather than supplied as a profile. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroOddMultiplicity
open Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7OddIntegral

theorem finite_count_prod {ι α M : Type*} [Fintype ι] [DecidableEq α]
    [CommMonoid M] (s : Multiset α) (e : ι → α) (he : Function.Injective e)
    (hcover : ∀ a ∈ s, ∃ i, e i = a) (f : α → M) :
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
      · subst j
        simp
      · have hne : e j ≠ e i := fun hji => h (he hji)
        simp only [Multiset.count_cons_of_ne hne, ite_eq_right h, Nat.add_zero]
    have hd (j : ι) : f (e j) ^ (if j = i then 1 else 0 : ℕ) =
        if j = i then f (e j) else 1 := by
      by_cases h : j = i <;> simp [h]
    calc
      ((e i ::ₘ s).map f).prod = f (e i) * (s.map f).prod := by
        rw [Multiset.map_cons, Multiset.prod_cons]
      _ = (∏ j, f (e j) ^ s.count (e j)) * f (e i) := by
        rw [ih hs]
        exact mul_comm _ _
      _ = ∏ j, f (e j) ^ (e i ::ₘ s).count (e j) := by
        simp_rw [hc, pow_add, hd]
        rw [Finset.prod_mul_distrib]
        simp
#print axioms Paper7IntroOddMultiplicity.finite_count_prod

theorem graphPhi_eq_integerSpectrum_prod
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G) :
    graphPhi G = ((integerSpectrum G).map (fun z : ℤ => X - C z)).prod := by
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  rw [Paper7Spectrum.graphPhi_map G ℝ]
  calc
    (G.adjMatrix ℝ).charpoly = ((spec G).map (fun z : ℝ => X - C z)).prod :=
      (Paper7Spectrum.realAdjHermitian G).splits_charpoly.eq_prod_roots_of_monic
        (G.adjMatrix ℝ).charpoly_monic
    _ = _ := by
      rw [← integerSpectrum_cast G hI]
      simp only [Polynomial.map_multiset_prod, Multiset.map_map,
        Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
#print axioms Paper7IntroOddMultiplicity.graphPhi_eq_integerSpectrum_prod

theorem intro21_graphPhi_window_product
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    graphPhi G = ∏ i : Fin 9,
      (X - C (integerWindowValue i)) ^ (integerSpectrum G).count (integerWindowValue i) := by
  rw [graphPhi_eq_integerSpectrum_prod G hI]
  exact finite_count_prod (integerSpectrum G) integerWindowValue
    integerWindowValue_injective (intro21_integerSpectrum_cover G b hG hI hn)
    (fun z : ℤ => X - C z)
#print axioms Paper7IntroOddMultiplicity.intro21_graphPhi_window_product

theorem intro21_graphPhi_nine_factors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    graphPhi G =
      (X + 4) ^ (integerSpectrum G).count (-4) *
      (X + 3) ^ (integerSpectrum G).count (-3) *
      (X + 2) ^ (integerSpectrum G).count (-2) *
      (X + 1) ^ (integerSpectrum G).count (-1) *
      X ^ (integerSpectrum G).count 0 *
      (X - 1) ^ (integerSpectrum G).count 1 *
      (X - 2) ^ (integerSpectrum G).count 2 *
      (X - 3) ^ (integerSpectrum G).count 3 *
      (X - 4) ^ (integerSpectrum G).count 4 := by
  have h := intro21_graphPhi_window_product G b hG hI hn
  norm_num [Fin.prod_univ_succ, integerWindowValue] at h
  simpa only [mul_assoc] using h
#print axioms Paper7IntroOddMultiplicity.intro21_graphPhi_nine_factors

end Paper7IntroOddMultiplicity
