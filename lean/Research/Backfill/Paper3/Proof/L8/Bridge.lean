import Research.Backfill.Paper3.Proof.L8.Poly

/-!
# Lemma 8, part 4: the law of a sum of i.i.d. variables with a finitely supported law

For `p : PMF ℕ` supported on `{0, …, M}` let `lawm p m` be the `m`-fold convolution of `p`.
If `ξ₁, …, ξ_m` are independent with law `p` then `Σ ξ_i` has law `lawm p m` (induction on `m`:
the partial sum is independent of the last variable, `IndepFun.hasLaw_add`), and
`lawm p m {s}` is the coefficient of `z^s` in `(Σ_i p(i) z^i)^m` (convolution formula on `ℕ`).
Also: integrals against `p` are finite sums.
-/

set_option autoImplicit false

namespace P3L8

open MeasureTheory ProbabilityTheory Polynomial Finset

/-- The `m`-fold convolution of `p`: the law of a sum of `m` independent variables with law `p`. -/
noncomputable def lawm (p : PMF ℕ) : ℕ → Measure ℕ
  | 0 => Measure.dirac 0
  | m + 1 => lawm p m ∗ p.toMeasure

instance isProbabilityMeasure_lawm (p : PMF ℕ) (m : ℕ) : IsProbabilityMeasure (lawm p m) := by
  induction m with
  | zero =>
    show IsProbabilityMeasure (Measure.dirac 0)
    infer_instance
  | succ m ih =>
    show IsProbabilityMeasure (lawm p m ∗ p.toMeasure)
    infer_instance

/-- The sum of `m` independent variables with law `p` has law `lawm p m`. -/
theorem hasLaw_sum (p : PMF ℕ) :
    ∀ (m : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ξ : Fin m → Ω → ℕ), iIndepFun ξ P → (∀ i, HasLaw (ξ i) p.toMeasure P) →
        HasLaw (fun ω => ∑ i, ξ i ω) (lawm p m) P := by
  intro m
  induction m with
  | zero =>
    intro Ω _ P _ ξ _ _
    show HasLaw (fun ω => ∑ i, ξ i ω) (Measure.dirac 0) P
    apply hasLaw_dirac_of_ae_eq
    exact Filter.Eventually.of_forall (fun ω => by simp)
  | succ m ih =>
    intro Ω _ P _ ξ hind hlaw
    have hη := ih P (fun i => ξ (Fin.castSucc i)) (hind.precomp (Fin.castSucc_injective m))
      (fun i => hlaw _)
    have hmeas : ∀ i, AEMeasurable (ξ i) P := fun i => (hlaw i).aemeasurable
    have hnot : Fin.last m ∉ (univ : Finset (Fin m)).map Fin.castSuccEmb := by
      rw [Finset.mem_map]
      rintro ⟨i, _, hi⟩
      exact (Fin.castSucc_lt_last i).ne hi
    have hind2 := hind.indepFun_finsetSum_of_notMem₀ hmeas hnot
    have hfun : (∑ j ∈ (univ : Finset (Fin m)).map Fin.castSuccEmb, ξ j) =
        fun ω => ∑ i, ξ (Fin.castSucc i) ω := by
      funext ω
      rw [Finset.sum_apply, Finset.sum_map]
      rfl
    rw [hfun] at hind2
    have hadd := IndepFun.hasLaw_add hη (hlaw (Fin.last m)) hind2
    have heq : (fun ω => ∑ i : Fin (m + 1), ξ i ω) =
        (fun ω => ∑ i, ξ (Fin.castSucc i) ω) + ξ (Fin.last m) := by
      funext ω
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [heq]
    exact hadd

/-- The convolution formula for measures on `ℕ`. -/
theorem conv_singleton (μ ν : Measure ℕ) [SFinite ν] (s : ℕ) :
    (μ ∗ ν) {s} = ∑ z ∈ antidiagonal s, μ {z.1} * ν {z.2} := by
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton s)]
  have hset : (fun x : ℕ × ℕ => x.1 + x.2) ⁻¹' {s} = ↑(antidiagonal s) := by
    ext z
    simp [Finset.HasAntidiagonal.mem_antidiagonal]
  rw [hset, ← sum_measure_singleton]
  apply sum_congr rfl
  rintro ⟨i, j⟩ _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

/-- `lawm p m {s}` is the coefficient of `z^s` in `(Σ_i p(i) z^i)^m`. -/
theorem lawm_singleton (p : PMF ℕ) (M : ℕ) (hsupp : ∀ i, M < i → p i = 0) :
    ∀ m s : ℕ, lawm p m {s} = ENNReal.ofReal ((gpoly (fun i => (p i).toReal) M ^ m).coeff s) := by
  have hnn : ∀ i, 0 ≤ (p i).toReal := fun i => ENNReal.toReal_nonneg
  intro m
  induction m with
  | zero =>
    intro s
    show Measure.dirac 0 {s} = _
    rw [pow_zero, coeff_one, Measure.dirac_apply]
    by_cases h : s = 0
    · subst h
      simp
    · simp [h, Ne.symm h]
  | succ m ih =>
    intro s
    show (lawm p m ∗ p.toMeasure) {s} = _
    rw [conv_singleton, pow_succ, coeff_mul, ENNReal.ofReal_sum_of_nonneg
      (fun z _ => mul_nonneg (coeff_gpoly_pow_nonneg _ hnn M m _) (coeff_gpoly_nonneg _ hnn M _))]
    apply sum_congr rfl
    intro z _
    rw [ih, ENNReal.ofReal_mul (coeff_gpoly_pow_nonneg _ hnn M m _),
      PMF.toMeasure_apply_singleton p _ (measurableSet_singleton _)]
    congr 1
    rw [coeff_gpoly]
    split_ifs with h
    · rw [ENNReal.ofReal_toReal (p.apply_ne_top _)]
    · simp only [mem_range, not_lt] at h
      rw [hsupp z.2 (by omega), ENNReal.ofReal_zero]

/-- A finite set `W ⊆ A` gives the lower bound `Σ_{s ∈ W} [z^s] f^m ≤ P(Σ ξ_i ∈ A)`. -/
theorem prob_ge_sum (p : PMF ℕ) (M : ℕ) (hsupp : ∀ i, M < i → p i = 0) (m : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Fin m → Ω → ℕ)
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) p.toMeasure P) (A : Set ℕ) (W : Finset ℕ)
    (hW : ∀ s ∈ W, s ∈ A) :
    ∑ s ∈ W, (gpoly (fun i => (p i).toReal) M ^ m).coeff s ≤
      (P {ω | (∑ i, ξ i ω) ∈ A}).toReal := by
  have hL := hasLaw_sum p m P ξ hind hlaw
  have hA : P {ω | (∑ i, ξ i ω) ∈ A} = lawm p m A :=
    hL.measure_eq (p := fun s => s ∈ A) MeasurableSet.of_discrete
  rw [hA]
  have hnn : ∀ s ∈ W, 0 ≤ (gpoly (fun i => (p i).toReal) M ^ m).coeff s :=
    fun s _ => coeff_gpoly_pow_nonneg _ (fun _ => ENNReal.toReal_nonneg) M m s
  have h1 : ENNReal.ofReal (∑ s ∈ W, (gpoly (fun i => (p i).toReal) M ^ m).coeff s) ≤
      lawm p m A := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    simp_rw [← lawm_singleton p M hsupp m]
    rw [sum_measure_singleton]
    exact measure_mono (fun s hs => hW s hs)
  calc ∑ s ∈ W, (gpoly (fun i => (p i).toReal) M ^ m).coeff s
      = (ENNReal.ofReal (∑ s ∈ W, (gpoly (fun i => (p i).toReal) M ^ m).coeff s)).toReal :=
        (ENNReal.toReal_ofReal (sum_nonneg hnn)).symm
    _ ≤ (lawm p m A).toReal := ENNReal.toReal_mono (measure_ne_top _ _) h1

/-- Integrals against a PMF on `ℕ` supported on `{0, …, M}` are finite sums. -/
theorem integral_pmf (p : PMF ℕ) (M : ℕ) (hsupp : ∀ i, M < i → p i = 0) (f : ℕ → ℝ) :
    ∫ i, f i ∂p.toMeasure = ∑ i ∈ range (M + 1), (p i).toReal * f i := by
  have hrestr : p.toMeasure.restrict ↑(range (M + 1)) = p.toMeasure := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff p MeasurableSet.of_discrete, Set.disjoint_left]
    intro i hi hi'
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_range, not_lt] at hi'
    exact (PMF.mem_support_iff p i).mp hi (hsupp i (by omega))
  rw [← hrestr, setIntegral_finset _ IntegrableOn.finset]
  apply sum_congr rfl
  intro i _
  rw [smul_eq_mul, measureReal_def, PMF.toMeasure_apply_singleton p i (measurableSet_singleton i)]

theorem sum_toReal_eq_one (p : PMF ℕ) (M : ℕ) (hsupp : ∀ i, M < i → p i = 0) :
    ∑ i ∈ range (M + 1), (p i).toReal = 1 := by
  have h := integral_pmf p M hsupp (fun _ => (1 : ℝ))
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_one] at h
  exact h.symm

end P3L8
