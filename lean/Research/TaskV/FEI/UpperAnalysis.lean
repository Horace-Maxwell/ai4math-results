import Research.TaskV.FEI.UpperChallenge

namespace Fei
open Finset

private lemma entropy_dc_le {p : ℝ} (hp : 0 ≤ p) (h1 : p ≤ 1) :
    p * (-Real.logb 2 p) ≤ 2 * (1 - p) := by
  rcases hp.eq_or_lt with heq | hpos
  · subst p
    norm_num
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne'] at hmul
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hprod := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * (1-p) by linarith)
  rw [Real.logb, ← neg_div, ← mul_div_assoc]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

-- The layer summation and divisibility-to-log implications are supplied by the final check.
set_option maxHeartbeats 800000 in
theorem comparableMassFEI_core
    (hLayer : ∀ (n : ℕ) (u : Finset (Cube n)) (a b : Cube n → ℝ),
      (∀ s ∈ u, 0 ≤ a s) →
      (∀ r : ℝ, 0 < r → ∑ s ∈ u.filter (fun s => r ≤ a s), b s ≤ 0) →
      ∑ s ∈ u, a s * b s ≤ 0)
    (hp : ∀ (n : ℕ) (f : Cube n → Bool), ∑ s ∈ support f, mass f s = 1)
    (hlog : ∀ (n : ℕ) (f : Cube n → Bool) (V : Finset (Cube n)),
      V ⊆ support f → (∀ s ∈ V, ∀ t ∈ support f, s ⊆ t → t ∈ V) →
      (∑ s ∈ V, -Real.logb 2 (mass f s)) + 2 * ((V.erase ∅).card : ℝ) ≤
        (4 : ℝ) * (∑ s ∈ V, s.card : ℕ)) : ComparableMassFEI := by
  classical
  intro n f L _hL hdist
  let u := (support f).erase ∅
  let pred (s : Cube n) := insert s (u.filter (fun t => t ⊆ s))
  let a (s : Cube n) := (pred s).sup' (Finset.insert_nonempty _ _) (mass f)
  have hself (s : Cube n) : mass f s ≤ a s :=
    Finset.le_sup' (mass f) (Finset.mem_insert_self s _)
  have ha (s : Cube n) : 0 ≤ a s := (sq_nonneg _).trans (hself s)
  have hpred (s : Cube n) (hs : s ∈ u) (v : Cube n) (hv : v ∈ pred s) :
      v ∈ u ∧ v ⊆ s := by
    rcases Finset.mem_insert.mp hv with h | h
    · subst v; exact ⟨hs, Finset.Subset.rfl⟩
    · exact Finset.mem_filter.mp h
  have hupper (s : Cube n) (hs : s ∈ u) : a s ≤ L * mass f s := by
    apply Finset.sup'_le
    intro v hv
    have h := hpred s hs v hv
    exact hdist v h.1 s hs h.2
  have hmono (s t : Cube n) (hs : s ∈ u) (hst : s ⊆ t) : a s ≤ a t := by
    apply Finset.sup'_le
    intro v hv
    obtain ⟨hvu, hvs⟩ := hpred s hs v hv
    have hmem : v ∈ u.filter (fun q => q ⊆ t) := Finset.mem_filter.mpr ⟨hvu, hvs.trans hst⟩
    have hv' : v ∈ pred t := Finset.mem_insert.mpr (Or.inr hmem)
    exact Finset.le_sup' (mass f) hv'
  have hmass (s : Cube n) (hs : s ∈ support f) : mass f s ≤ 1 := by
    rw [← hp n f]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (coeff f i)) hs
  let cost (s : Cube n) := -Real.logb 2 (mass f s) + 2
  have hcost (s : Cube n) (hs : s ∈ u) : 0 ≤ cost s := by
    have h := Real.logb_nonpos (by norm_num : (1:ℝ)<2) (sq_nonneg (coeff f s))
      (hmass s (Finset.mem_of_mem_erase hs))
    change Real.logb 2 (mass f s) ≤ 0 at h
    dsimp [cost]
    linarith
  have hlayer := hLayer n u a (fun s => cost s - 4 * s.card) (fun s _ => ha s) (by
    intro r _hr
    let V := u.filter (fun s => r ≤ a s)
    have hsub (s : Cube n) (hs : s ∈ V) : s ∈ u := (Finset.mem_filter.mp hs).1
    have hV : V ⊆ support f := fun s hs => Finset.mem_of_mem_erase (hsub s hs)
    have up : ∀ s ∈ V, ∀ t ∈ support f, s ⊆ t → t ∈ V := by
      intro s hs t ht hst
      have hs' := hsub s hs
      have htne : t ≠ ∅ := by
        intro he; subst t
        exact Finset.ne_of_mem_erase hs' (Finset.subset_empty.mp hst)
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htne,ht⟩,
        (Finset.mem_filter.mp hs).2.trans (hmono s t hs' hst)⟩
    have hno : ∅ ∉ V := fun h => Finset.ne_of_mem_erase (hsub _ h) rfl
    have hVlog := hlog n f V hV up
    rw [Finset.erase_eq_of_notMem hno] at hVlog
    change ∑ s ∈ V, (cost s - 4 * (s.card : ℝ)) ≤ 0
    simp only [cost, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum, ← Nat.cast_sum]
    linarith)
  have hweight :
      (∑ s ∈ u, a s * cost s) ≤ ∑ s ∈ u, a s * (4 * (s.card : ℝ)) := by
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_nonpos] using hlayer
  have hpart : entropy f ≤ ∑ s ∈ u, mass f s * cost s := by
    simp only [cost, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    by_cases he : ∅ ∈ support f
    · have hpsum := Finset.sum_erase_add (support f) (mass f) he
      have hentsum := Finset.sum_erase_add (support f)
        (fun s => mass f s * (-Real.logb 2 (mass f s))) he
      have hdc := entropy_dc_le (p := mass f ∅) (sq_nonneg (coeff f ∅)) (hmass ∅ he)
      change (∑ s ∈ support f, mass f s * (-Real.logb 2 (mass f s))) ≤ _
      dsimp [u]
      linarith [hp n f]
    · simp only [u, Finset.erase_eq_of_notMem he, hp n f, entropy]
      linarith
  have hIsum : ∑ s ∈ u, mass f s * (s.card : ℝ) = influence f := by
    by_cases he : ∅ ∈ support f
    · simpa only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero, influence, u] using
        (Finset.sum_erase_add (support f) (fun s => mass f s * (s.card : ℝ)) he)
    · simp [u, Finset.erase_eq_of_notMem he, influence]
  calc
    entropy f ≤ _ := hpart
    _ ≤ ∑ s ∈ u, a s * cost s :=
      Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_right (hself s) (hcost s hs)
    _ ≤ _ := hweight
    _ ≤ ∑ s ∈ u, (4 * L) * (mass f s * (s.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have h := mul_le_mul_of_nonneg_right (hupper s hs)
        (show 0 ≤ (4:ℝ) * s.card by positivity)
      linarith
    _ = _ := by rw [← Finset.mul_sum, hIsum]

end Fei
