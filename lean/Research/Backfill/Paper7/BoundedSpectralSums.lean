import Research.Backfill.Paper7.LegacyCandidates
import Research.Backfill.Paper7.SpectralMoments

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
Finite multiplicity expansions of the actual bounded integral spectrum.
No compilation, independent acceptance, or complete pruning check is claimed.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7PruningSpectrum
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

/-- Expand a multiset over any injective finite enumeration of its support. -/
theorem finite_count_sum {ι α M : Type*} [Fintype ι] [DecidableEq α]
    [AddCommMonoid M] (s : Multiset α) (e : ι → α) (he : Function.Injective e)
    (hcover : ∀ a ∈ s, ∃ i, e i = a) (f : α → M) :
    (s.map f).sum = ∑ i, s.count (e i) • f (e i) := by
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
    have hd (j : ι) : ((if j = i then 1 else 0 : ℕ) • f (e j)) =
        if j = i then f (e j) else 0 := by
      by_cases h : j = i <;> simp [h]
    calc
      ((e i ::ₘ s).map f).sum = f (e i) + (s.map f).sum := by
        rw [Multiset.map_cons, Multiset.sum_cons]
      _ = (∑ j, s.count (e j) • f (e j)) + f (e i) := by
        rw [ih hs]
        exact add_comm _ _
      _ = ∑ j, (e i ::ₘ s).count (e j) • f (e j) := by
        simp_rw [hc, add_nsmul, hd]
        rw [Finset.sum_add_distrib]
        simp
#print axioms Paper7PruningSpectrum.finite_count_sum

theorem finite_count_card {ι α : Type*} [Fintype ι] [DecidableEq α]
    (s : Multiset α) (e : ι → α) (he : Function.Injective e)
    (hcover : ∀ a ∈ s, ∃ i, e i = a) :
    s.card = ∑ i, s.count (e i) := by
  simpa only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one,
    Nat.cast_id] using
    finite_count_sum s e he hcover (fun _ => (1 : ℕ))
#print axioms Paper7PruningSpectrum.finite_count_card

theorem value_real_injective :
    Function.Injective (fun i : Fin 8 => (value i : ℝ)) := by
  intro i j hij
  change (value i : ℝ) = (value j : ℝ) at hij
  have hv : value i = value j := by exact_mod_cast hij
  apply Fin.ext
  dsimp [value] at hv
  omega
#print axioms Paper7PruningSpectrum.value_real_injective

theorem neg_value_real_injective :
    Function.Injective (fun i : Fin 8 => -(value i : ℝ)) := by
  intro i j hij
  apply value_real_injective
  have h := congrArg (fun x : ℝ => -x) hij
  simpa only [neg_neg] using h
#print axioms Paper7PruningSpectrum.neg_value_real_injective

theorem value_lower_bound (i : Fin 8) : (2 : ℝ) ≤ (value i : ℝ) := by
  have h : 2 ≤ value i := by dsimp [value]; omega
  exact_mod_cast h
#print axioms Paper7PruningSpectrum.value_lower_bound

theorem positive_value_rep (x : ℝ) (hx : ∃ z : ℤ, x = (z : ℝ))
    (h2 : 2 ≤ x) (h10 : x < 10) : ∃ i : Fin 8, (value i : ℝ) = x := by
  obtain ⟨z, hz⟩ := hx
  have hz2 : (2 : ℤ) ≤ z := by
    rw [hz] at h2
    exact_mod_cast h2
  have hz10 : z < (10 : ℤ) := by
    rw [hz] at h10
    exact_mod_cast h10
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  let i : Fin 8 := ⟨z.toNat - 2, by omega⟩
  have hi : value i = z.toNat := by
    dsimp [value, i]
    omega
  refine ⟨i, ?_⟩
  rw [hi]
  have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
  exact hc.trans hz.symm
#print axioms Paper7PruningSpectrum.positive_value_rep

theorem negative_value_rep (x : ℝ) (hx : ∃ z : ℤ, x = (z : ℝ))
    (h2 : x ≤ -2) (h10 : -10 < x) : ∃ i : Fin 8, -(value i : ℝ) = x := by
  have hneg : ∃ z : ℤ, -x = (z : ℝ) := by
    obtain ⟨z, hz⟩ := hx
    refine ⟨-z, ?_⟩
    simp only [hz, Int.cast_neg]
  obtain ⟨i, hi⟩ := positive_value_rep (-x) hneg (by linarith) (by linarith)
  refine ⟨i, ?_⟩
  have h := congrArg (fun a : ℝ => -a) hi
  simpa only [neg_neg] using h
#print axioms Paper7PruningSpectrum.negative_value_rep

theorem positive_support {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    ∀ a ∈ Bplus G, ∃ i : Fin 8, (value i : ℝ) = a := by
  intro a ha
  obtain ⟨hs, h2⟩ := Multiset.mem_filter.mp ha
  exact positive_value_rep a (Paper7Moments.integral_spec_entry G hG a hs)
    h2 (abs_lt.mp (hwin a hs)).2
#print axioms Paper7PruningSpectrum.positive_support

theorem negative_support {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    ∀ a ∈ (spec G).filter (fun x => x ≤ -2), ∃ i : Fin 8, -(value i : ℝ) = a := by
  intro a ha
  obtain ⟨hs, h2⟩ := Multiset.mem_filter.mp ha
  exact negative_value_rep a (Paper7Moments.integral_spec_entry G hG a hs)
    h2 (abs_lt.mp (hwin a hs)).1
#print axioms Paper7PruningSpectrum.negative_support

theorem positive_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (f : ℝ → ℝ) :
    ((Bplus G).map f).sum =
      ∑ i : Fin 8, (mult G (value i) : ℝ) * f (value i) := by
  classical
  calc
    ((Bplus G).map f).sum =
        ∑ i : Fin 8, (Bplus G).count (value i : ℝ) • f (value i) :=
      finite_count_sum (Bplus G) (fun i : Fin 8 => (value i : ℝ))
        value_real_injective (positive_support G hG hwin) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hc : (Bplus G).count (value i : ℝ) = mult G (value i) :=
        Multiset.count_filter_of_pos (value_lower_bound i)
      rw [hc]
      exact nsmul_eq_mul _ _
#print axioms Paper7PruningSpectrum.positive_sum

theorem negative_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (f : ℝ → ℝ) :
    (((spec G).filter (fun x => x ≤ -2)).map f).sum =
      ∑ i : Fin 8, (mult G (-(value i : ℝ)) : ℝ) * f (-(value i : ℝ)) := by
  classical
  calc
    (((spec G).filter (fun x => x ≤ -2)).map f).sum =
        ∑ i : Fin 8, ((spec G).filter (fun x => x ≤ -2)).count (-(value i : ℝ)) •
          f (-(value i : ℝ)) :=
      finite_count_sum ((spec G).filter (fun x => x ≤ -2))
        (fun i : Fin 8 => -(value i : ℝ)) neg_value_real_injective
        (negative_support G hG hwin) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := value_lower_bound i
      have hc : ((spec G).filter (fun x => x ≤ -2)).count (-(value i : ℝ)) =
          mult G (-(value i : ℝ)) :=
        Multiset.count_filter_of_pos (by linarith : -(value i : ℝ) ≤ -2)
      rw [hc]
      exact nsmul_eq_mul _ _
#print axioms Paper7PruningSpectrum.negative_sum

theorem large_filter_split (s : Multiset ℝ) :
    s.filter (fun x => 2 ≤ |x|) =
      s.filter (fun x => 2 ≤ x) + s.filter (fun x => x ≤ -2) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    by_cases hp : 2 ≤ x
    · have hn : ¬ x ≤ -2 := by linarith
      have ha : 2 ≤ |x| := hp.trans (le_abs_self x)
      simp [hp, hn, ha, ih]
    · by_cases hn : x ≤ -2
      · have ha : 2 ≤ |x| := by
          rw [abs_of_nonpos (by linarith : x ≤ 0)]
          linarith
        simp [hp, hn, ha, ih]
      · have ha : ¬ 2 ≤ |x| := by
          apply not_le.mpr
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        simp [hp, hn, ha, ih]
#print axioms Paper7PruningSpectrum.large_filter_split

theorem big_sum {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) (f : ℝ → ℝ) :
    ((bigEigs G).map f).sum =
      (∑ i : Fin 8, (mult G (value i) : ℝ) * f (value i)) +
      ∑ i : Fin 8, (mult G (-(value i : ℝ)) : ℝ) * f (-(value i : ℝ)) := by
  change (((spec G).filter (fun x => 2 ≤ |x|)).map f).sum = _
  rw [large_filter_split, Multiset.map_add, Multiset.sum_add]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (positive_sum G hG hwin f) (negative_sum G hG hwin f)
#print axioms Paper7PruningSpectrum.big_sum

theorem positive_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    (Bplus G).card = ∑ i : Fin 8, mult G (value i) := by
  classical
  calc
    (Bplus G).card = ∑ i : Fin 8, (Bplus G).count (value i : ℝ) :=
      finite_count_card (Bplus G) (fun i : Fin 8 => (value i : ℝ))
        value_real_injective (positive_support G hG hwin)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Multiset.count_filter_of_pos (value_lower_bound i)
#print axioms Paper7PruningSpectrum.positive_card

theorem negative_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    ((spec G).filter (fun x => x ≤ -2)).card =
      ∑ i : Fin 8, mult G (-(value i : ℝ)) := by
  classical
  calc
    ((spec G).filter (fun x => x ≤ -2)).card =
        ∑ i : Fin 8, ((spec G).filter (fun x => x ≤ -2)).count (-(value i : ℝ)) :=
      finite_count_card ((spec G).filter (fun x => x ≤ -2))
        (fun i : Fin 8 => -(value i : ℝ)) neg_value_real_injective
        (negative_support G hG hwin)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := value_lower_bound i
      exact Multiset.count_filter_of_pos (by linarith : -(value i : ℝ) ≤ -2)
#print axioms Paper7PruningSpectrum.negative_card

theorem positive_filter_eq_threshold {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G) :
    Bplus G = (spec G).filter (fun x => 1 < x) := by
  classical
  apply Multiset.filter_congr
  intro a ha
  obtain ⟨z, rfl⟩ := Paper7Moments.integral_spec_entry G hG a ha
  constructor
  · intro h
    linarith
  · intro h
    have hz : (1 : ℤ) < z := by exact_mod_cast h
    have hz2 : (2 : ℤ) ≤ z := by omega
    exact_mod_cast hz2
#print axioms Paper7PruningSpectrum.positive_filter_eq_threshold

theorem negative_filter_eq_threshold {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G) :
    (spec G).filter (fun x => x ≤ -2) = (spec G).filter (fun x => x < -1) := by
  classical
  apply Multiset.filter_congr
  intro a ha
  obtain ⟨z, rfl⟩ := Paper7Moments.integral_spec_entry G hG a ha
  constructor
  · intro h
    linarith
  · intro h
    have hz : z < (-1 : ℤ) := by exact_mod_cast h
    have hz2 : z ≤ (-2 : ℤ) := by omega
    exact_mod_cast hz2
#print axioms Paper7PruningSpectrum.negative_filter_eq_threshold

theorem positive_threshold {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    Ngt G 1 = ∑ i : Fin 8, mult G (value i) := by
  change ((spec G).filter (fun x => 1 < x)).card = _
  rw [← positive_filter_eq_threshold G hG]
  exact positive_card G hG hwin
#print axioms Paper7PruningSpectrum.positive_threshold

theorem negative_threshold {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hwin : ∀ a ∈ spec G, |a| < 10) :
    Nlt G (-1) = ∑ i : Fin 8, mult G (-(value i : ℝ)) := by
  change ((spec G).filter (fun x => x < -1)).card = _
  rw [← negative_filter_eq_threshold G hG]
  exact negative_card G hG hwin
#print axioms Paper7PruningSpectrum.negative_threshold

end Paper7PruningSpectrum
