import Research.Backfill.Paper3.Proof.CD.Markov

/-!
# The law of `ξ` and the use of Lemma 8

`ξ` is the number of edges of `K_{d,d}` spanned by a uniform vertex set (`lawXi`, a `PMF ℕ`
supported on `{0, …, d²}`, with mean `d²/4` and `E e^{λξ} = P_d(e^λ)/4^d`). For each `m` the
product space `Fin m → Finset (Fin d ⊕ Fin d)` with `Measure.pi` of uniform measures carries
independent copies `ξ_i(ω) = e(ω_i)` (`iIndepFun_pi`); its events are counted and transported
to vertex sets of `m K_{d,d}` by `P3Basic.fibresEquiv`. Lemma 8 (a), (b) then give the lower
bounds `upper_tail` and `lower_tail` on the number of vertex sets of `m K_{d,d}` spanning more
(fewer) than `m x` edges.
-/

set_option autoImplicit false

namespace P3CD

open Finset SimpleGraph Polynomial MeasureTheory ProbabilityTheory Filter
open BackfillPaper3.Challenge P3Basic
open scoped ENNReal

/-- The vertex sets of `K_{d,d}`. -/
abbrev KS (d : ℕ) : Type := Finset (Fin d ⊕ Fin d)

theorem card_KS (d : ℕ) : Fintype.card (KS d) = 4 ^ d := by
  simp only [KS, Fintype.card_finset, Fintype.card_sum, Fintype.card_fin]
  rw [← two_mul, pow_mul]
  norm_num

/-- The law of `ξ`. -/
noncomputable def lawXi (d : ℕ) : PMF ℕ := (PMF.uniformOfFintype (KS d)).map (edgesIn (Kdd d))

theorem measurable_edgesIn (d : ℕ) : Measurable (edgesIn (Kdd d) : KS d → ℕ) :=
  Measurable.of_discrete

/-- Expectations against the law of `ξ` are averages over the vertex sets of `K_{d,d}`. -/
theorem integral_lawXi (d : ℕ) (f : ℕ → ℝ) :
    ∫ i, f i ∂(lawXi d).toMeasure = (∑ A : KS d, f (edgesIn (Kdd d) A)) / 4 ^ d := by
  unfold lawXi
  rw [← PMF.toMeasure_map _ _ (measurable_edgesIn d),
    integral_map (measurable_edgesIn d).aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    PMF.integral_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [PMF.uniformOfFintype_apply, card_KS, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  push_cast
  ring

theorem mean_lawXi (d : ℕ) (hd : 1 ≤ d) : ∫ i, (i : ℝ) ∂(lawXi d).toMeasure = (d : ℝ) ^ 2 / 4 := by
  rw [integral_lawXi d (fun i => (i : ℝ)), sum_Kdd d (fun s => (s : ℝ)), sum_wt_mul, mean_eq d hd]
  field_simp

theorem mgf_lawXi (d : ℕ) (l : ℝ) :
    ∫ i, Real.exp (l * i) ∂(lawXi d).toMeasure = Pf d (Real.exp l) / 4 ^ d := by
  rw [integral_lawXi d (fun i => Real.exp (l * i)), Pf_eq_sum_Kdd]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [mul_comm, Real.exp_nat_mul]

theorem edgesIn_Kdd_le (d : ℕ) (A : KS d) : edgesIn (Kdd d) A ≤ d ^ 2 := by
  have h := edgesIn_Kdd d A.toLeft A.toRight
  rw [Finset.toLeft_disjSum_toRight] at h
  rw [h, sq]
  exact Nat.mul_le_mul (card_le_univ _ |>.trans (by simp)) (card_le_univ _ |>.trans (by simp))

theorem lawXi_ne_zero_iff (d i : ℕ) : lawXi d i ≠ 0 ↔ ∃ A : KS d, edgesIn (Kdd d) A = i := by
  rw [← PMF.mem_support_iff, lawXi, PMF.mem_support_map_iff]
  simp

theorem lawXi_supp (d : ℕ) : ∀ i, d ^ 2 < i → lawXi d i = 0 := by
  intro i hi
  by_contra h
  obtain ⟨A, hA⟩ := (lawXi_ne_zero_iff d i).1 h
  have := edgesIn_Kdd_le d A
  omega

theorem lawXi_zero (d : ℕ) : lawXi d 0 ≠ 0 :=
  (lawXi_ne_zero_iff d 0).2 ⟨∅, edgesIn_empty _⟩

theorem lawXi_top (d : ℕ) : lawXi d (d ^ 2) ≠ 0 := by
  refine (lawXi_ne_zero_iff d _).2 ⟨univ, ?_⟩
  have h := edgesIn_Kdd d univ univ
  rw [Finset.univ_disjSum_univ] at h
  rw [h]
  simp [sq]

/-! ### The product space -/

/-- The uniform probability measure on the vertex sets of `K_{d,d}`. -/
noncomputable def muK (d : ℕ) : Measure (KS d) := (PMF.uniformOfFintype (KS d)).toMeasure

instance (d : ℕ) : IsProbabilityMeasure (muK d) := by
  unfold muK
  infer_instance

/-- `m` independent uniform vertex sets of `K_{d,d}`. -/
noncomputable def PP (d m : ℕ) : Measure (Fin m → KS d) := Measure.pi fun _ => muK d

instance (d m : ℕ) : IsProbabilityMeasure (PP d m) := by
  unfold PP
  infer_instance

/-- `ξ_i(ω) = e_{K_{d,d}}(ω_i)`. -/
def xi (d m : ℕ) (i : Fin m) (ω : Fin m → KS d) : ℕ := edgesIn (Kdd d) (ω i)

theorem xi_indep (d m : ℕ) : iIndepFun (xi d m) (PP d m) :=
  iIndepFun_pi (μ := fun _ => muK d) (X := fun _ => edgesIn (Kdd d))
    fun _ => (measurable_edgesIn d).aemeasurable

theorem xi_law (d m : ℕ) (i : Fin m) : HasLaw (xi d m i) (lawXi d).toMeasure (PP d m) := by
  have h1 : MeasurePreserving (edgesIn (Kdd d)) (muK d) (lawXi d).toMeasure :=
    ⟨measurable_edgesIn d, PMF.toMeasure_map _ _ (measurable_edgesIn d)⟩
  exact (h1.comp (measurePreserving_eval (fun _ => muK d) i)).hasLaw

theorem PP_singleton (d m : ℕ) (ω : Fin m → KS d) :
    PP d m {ω} = ((4 ^ d : ℕ) : ℝ≥0∞)⁻¹ ^ m := by
  rw [PP, Measure.pi_singleton]
  simp only [muK, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, card_KS, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem PP_real (d m : ℕ) (p : (Fin m → KS d) → Prop) [DecidablePred p] :
    (PP d m {ω | p ω}).toReal = (#(univ.filter p) : ℝ) / ((4 : ℝ) ^ d) ^ m := by
  have hset : {ω | p ω} = ((univ.filter p : Finset (Fin m → KS d)) : Set (Fin m → KS d)) := by
    ext ω
    simp
  rw [hset, ← sum_measure_singleton]
  simp only [PP_singleton, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, inv_pow, ← div_eq_mul_inv]
  push_cast
  rfl

/-- Events on the product space are events on the vertex sets of `m K_{d,d}`. -/
theorem card_event (d m : ℕ) (R : ℕ → Prop) [DecidablePred R] :
    #(univ.filter fun ω : Fin m → KS d => R (∑ i, xi d m i ω)) =
      #(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        R (edgesIn (KddUnion m d) A)) := by
  refine Finset.card_equiv (fibresEquiv m (Fin d ⊕ Fin d)).symm (fun ω => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show edgesIn (KddUnion m d) ((fibresEquiv m (Fin d ⊕ Fin d)).symm ω) =
    ∑ i, edgesIn (Kdd d) (ω i) from edgesIn_copies m (Kdd d) ω]
  rfl

theorem four_pow_pow (d m : ℕ) : ((4 : ℝ) ^ d) ^ m = Real.exp (m * (d * Real.log 4)) := by
  rw [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity)]

/-! ### Lemma 8 applied to `m K_{d,d}` -/

/-- Upper tail (Lemma 8(a)): if `L ≤ log P_d(q) - x log q` for all `q ≥ 1`, then for every
`ε > 0` and all large `m`, at least `e^{m(L - ε)}` vertex sets of `m K_{d,d}` span more than
`m x` edges. -/
theorem upper_tail (h8 : Lemma8) {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx1 : (d : ℝ) ^ 2 / 4 < x)
    (hx2 : x < (d : ℝ) ^ 2) {L : ℝ}
    (hL : ∀ q : ℝ, 1 ≤ q → L ≤ Real.log (Pf d q) - x * Real.log q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, Real.exp (m * (L - ε)) ≤
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (m : ℝ) * x < (edgesIn (KddUnion m d) A : ℝ)) : ℝ) := by
  classical
  have h := (h8 (d ^ 2) (lawXi d) (lawXi_supp d) (lawXi_zero d) (lawXi_top d)).1 x
    (by rw [mean_lawXi d hd]; exact hx1) (by push_cast; exact hx2) ε hε
  filter_upwards [h] with m hm
  have hP := hm (Fin m → KS d) (PP d m) (xi d m) (xi_indep d m) (xi_law d m)
  have hinf : L - d * Real.log 4 ≤ ⨅ l : Set.Ici (0 : ℝ),
      (Real.log (∫ i, Real.exp (l * i) ∂(lawXi d).toMeasure) - l * x) := by
    apply le_ciInf
    rintro ⟨l, hl⟩
    rw [mgf_lawXi, Real.log_div (Pf_pos d (Real.exp_pos l).le).ne' (by positivity), Real.log_pow]
    have := hL (Real.exp l) (Real.one_le_exp hl)
    rw [Real.log_exp] at this
    linarith
  have hev : (PP d m {ω | (m : ℝ) * x < ∑ i, (xi d m i ω : ℝ)}).toReal =
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (m : ℝ) * x < (edgesIn (KddUnion m d) A : ℝ)) : ℝ) / ((4 : ℝ) ^ d) ^ m := by
    rw [PP_real]
    congr 2
    have := card_event d m (fun s => (m : ℝ) * x < (s : ℝ))
    rw [← this]
    congr 1
    ext ω
    simp
  rw [hev, le_div_iff₀ (by positivity)] at hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc Real.exp (m * (L - ε)) = Real.exp (m * (L - d * Real.log 4 - ε)) * ((4 : ℝ) ^ d) ^ m := by
        rw [four_pow_pow, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (m * ((⨅ l : Set.Ici (0 : ℝ),
          (Real.log (∫ i, Real.exp (l * i) ∂(lawXi d).toMeasure) - l * x)) - ε)) *
          ((4 : ℝ) ^ d) ^ m := by
        gcongr
    _ ≤ _ := hP

/-- Lower tail (Lemma 8(b)): if `L ≤ log P_d(q) - x log q` for all `q ∈ (0, 1]`, then for every
`ε > 0` and all large `m`, at least `e^{m(L - ε)}` vertex sets of `m K_{d,d}` span fewer than
`m x` edges. -/
theorem lower_tail (h8 : Lemma8) {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < (d : ℝ) ^ 2 / 4) {L : ℝ}
    (hL : ∀ q : ℝ, 0 < q → q ≤ 1 → L ≤ Real.log (Pf d q) - x * Real.log q) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, Real.exp (m * (L - ε)) ≤
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (edgesIn (KddUnion m d) A : ℝ) < m * x) : ℝ) := by
  classical
  have h := (h8 (d ^ 2) (lawXi d) (lawXi_supp d) (lawXi_zero d) (lawXi_top d)).2 x hx0
    (by rw [mean_lawXi d hd]; exact hx1) ε hε
  filter_upwards [h] with m hm
  have hP := hm (Fin m → KS d) (PP d m) (xi d m) (xi_indep d m) (xi_law d m)
  have hinf : L - d * Real.log 4 ≤ ⨅ l : Set.Iic (0 : ℝ),
      (Real.log (∫ i, Real.exp (l * i) ∂(lawXi d).toMeasure) - l * x) := by
    apply le_ciInf
    rintro ⟨l, hl⟩
    rw [mgf_lawXi, Real.log_div (Pf_pos d (Real.exp_pos l).le).ne' (by positivity), Real.log_pow]
    have := hL (Real.exp l) (Real.exp_pos l) (Real.exp_le_one_iff.2 hl)
    rw [Real.log_exp] at this
    linarith
  have hev : (PP d m {ω | ∑ i, (xi d m i ω : ℝ) < m * x}).toReal =
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (edgesIn (KddUnion m d) A : ℝ) < m * x) : ℝ) / ((4 : ℝ) ^ d) ^ m := by
    rw [PP_real]
    congr 2
    have := card_event d m (fun s => (s : ℝ) < m * x)
    rw [← this]
    congr 1
    ext ω
    simp
  rw [hev, le_div_iff₀ (by positivity)] at hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc Real.exp (m * (L - ε)) = Real.exp (m * (L - d * Real.log 4 - ε)) * ((4 : ℝ) ^ d) ^ m := by
        rw [four_pow_pow, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (m * ((⨅ l : Set.Iic (0 : ℝ),
          (Real.log (∫ i, Real.exp (l * i) ∂(lawXi d).toMeasure) - l * x)) - ε)) *
          ((4 : ℝ) ^ d) ^ m := by
        gcongr
    _ ≤ _ := hP

end P3CD
