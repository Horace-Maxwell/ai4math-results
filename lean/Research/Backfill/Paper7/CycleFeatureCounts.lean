import Research.Backfill.Paper7.LegacyCandidates
import Research.Backfill.Paper7.CycleCosineThreshold

/-! Source-only exact translation of both original cycle-filter counts.
The negative count is derived directly from the complete cycle cosine spectrum;
no symmetry of an odd sun graph is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningSpectrum
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy Paper7Lemma41

theorem card_fin_filter_range (b : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (univ.filter (fun i : Fin b => p i.val)).card = ((range b).filter p).card := by
  refine card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    exact mem_filter.mpr ⟨mem_range.mpr i.isLt, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, mem_range.mp (mem_filter.mp hj).1⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
#print axioms Paper7PruningSpectrum.card_fin_filter_range

theorem cyclicPositive_eq_Ngt (b : ℕ) (hb : 3 ≤ b) :
    cyclicPositive b = Ngt (SimpleGraph.cycleGraph b) 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n+3 := ⟨b-3, by omega⟩
  rw [cycleGraph_Ngt_one_frequency_count (n+3) hb]
  simp_rw [cycleCosine_gt_one_iff]
  change ((range (n+3)).filter (fun j => 6 * min j (n+3-j) < n+3)).card =
    (univ.filter (fun k : Fin (n+3) => 6*k.val < n+3 ∨ 6*(n+3-k.val) < n+3)).card
  have hf :
      (univ.filter (fun k : Fin (n+3) =>
        6*k.val < n+3 ∨ 6*(n+3-k.val) < n+3)) =
      (univ.filter (fun k : Fin (n+3) =>
        6 * min k.val (n+3-k.val) < n+3)) := by
    apply Finset.filter_congr
    intro k _
    omega
  rw [hf]
  exact (card_fin_filter_range (n+3)
    (fun j : ℕ => 6 * min j (n+3-j) < n+3)).symm
#print axioms Paper7PruningSpectrum.cyclicPositive_eq_Ngt

theorem two_cos_lt_neg_one_period (θ : ℝ) (h0 : 0 ≤ θ) (h2pi : θ ≤ 2 * Real.pi) :
    2 * Real.cos θ < -1 ↔ 3 * |θ - Real.pi| < Real.pi := by
  have ha : |θ-Real.pi| ≤ Real.pi := abs_le.mpr ⟨by linarith, by linarith⟩
  have h := two_cos_gt_one_first_half |θ-Real.pi| (abs_nonneg _) ha
  rw [Real.cos_abs, Real.cos_sub_pi] at h
  constructor
  · intro hc
    have ht := h.mp (by linarith)
    linarith
  · intro ht
    have hc := h.mpr (by linarith)
    linarith
#print axioms Paper7PruningSpectrum.two_cos_lt_neg_one_period

theorem centered_angle_iff (b j : ℕ) (hb : 0 < b) :
    3 * |2 * Real.pi * ((j : ℝ) / b) - Real.pi| < Real.pi ↔
      3 * |2 * (j : ℤ) - (b : ℤ)| < b := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hc : 0 < Real.pi / (b : ℝ) := div_pos Real.pi_pos hbR
  have heq : 2 * Real.pi * ((j : ℝ) / b) - Real.pi =
      (Real.pi / (b : ℝ)) * (2 * j - b) := by
    field_simp [ne_of_gt hbR]
  have hπ : (Real.pi / (b : ℝ)) * b = Real.pi := div_mul_cancel₀ _ (ne_of_gt hbR)
  have heqabs : 3 * |2 * Real.pi * ((j : ℝ) / b) - Real.pi| =
      (Real.pi / (b : ℝ)) * (3 * |2 * (j : ℝ) - b|) := by
    rw [heq, abs_mul, abs_of_pos hc]
    ring
  rw [heqabs]
  constructor
  · intro h
    have h' : (Real.pi / (b : ℝ)) * (3 * |2 * (j : ℝ) - b|) <
        (Real.pi / (b : ℝ)) * b := by rw [hπ]; exact h
    have h'' : 3 * |2 * (j : ℝ) - b| < (b : ℝ) :=
      (mul_lt_mul_iff_right₀ hc).mp h'
    exact_mod_cast h''
  · intro h
    have h' : 3 * |2 * (j : ℝ) - b| < (b : ℝ) := by exact_mod_cast h
    calc
      (Real.pi / (b : ℝ)) * (3 * |2 * (j : ℝ) - b|) <
          (Real.pi / (b : ℝ)) * b := (mul_lt_mul_iff_right₀ hc).mpr h'
      _ = Real.pi := hπ
#print axioms Paper7PruningSpectrum.centered_angle_iff

theorem cycleCosine_lt_neg_one_iff (b : ℕ) [NeZero b] (k : ZMod b) :
    cycleCosine b k < -1 ↔ 3 * |2 * (k.val : ℤ) - (b : ℤ)| < b := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hkR : (k.val : ℝ) ≤ b := by exact_mod_cast (ZMod.val_lt k).le
  have hfrac : (k.val : ℝ) / b ≤ 1 := (div_le_one hbR).mpr hkR
  have hθ0 : 0 ≤ 2 * Real.pi * ((k.val : ℝ) / b) := by positivity
  have hθ2 : 2 * Real.pi * ((k.val : ℝ) / b) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  rw [cycleCosine, two_cos_lt_neg_one_period _ hθ0 hθ2, centered_angle_iff b k.val hb]
#print axioms Paper7PruningSpectrum.cycleCosine_lt_neg_one_iff

theorem cyclicNegative_eq_Nlt (b : ℕ) (hb : 3 ≤ b) :
    cyclicNegative b = Nlt (SimpleGraph.cycleGraph b) (-1) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n+3 := ⟨b-3, by omega⟩
  have hcast : cyclicNegative (n+3) =
      ((range (n+3)).filter (fun j : ℕ =>
        3 * |2 * (j : ℤ)-((n+3 : ℕ) : ℤ)| < ((n+3 : ℕ) : ℤ))).card := by
    classical
    let : DecidableEq ℤ := Int.instDecidableEq
    have himage :
        @Finset.image ℕ ℤ (fun a b => Classical.propDecidable (a = b))
          (fun j : ℕ => (j : ℤ)) (range (n+3)) =
        @Finset.image ℕ ℤ Int.instDecidableEq
          (fun j : ℕ => (j : ℤ)) (range (n+3)) :=
      congrArg (fun d : DecidableEq ℤ =>
        @Finset.image ℕ ℤ d (fun j : ℕ => (j : ℤ)) (range (n+3)))
          (Subsingleton.elim _ _)
    unfold cyclicNegative
    rw [bind_pure_comp, Finset.fmap_def, himage, Finset.filter_image]
    exact Finset.card_image_of_injective _ (fun _ _ h => Int.natCast_inj.mp h)
  have hcount :
      (univ.filter (fun k : ZMod (n+3) =>
        3 * |2 * (k.val : ℤ)-((n+3 : ℕ) : ℤ)| < ((n+3 : ℕ) : ℤ))).card =
      ((range (n+3)).filter (fun j : ℕ =>
        3 * |2 * (j : ℤ)-((n+3 : ℕ) : ℤ)| < ((n+3 : ℕ) : ℤ))).card := by
    refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
    · intro k hk
      exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt k), (mem_filter.mp hk).2⟩
    · intro i _hi j _hj hij
      exact ZMod.val_injective (n+3) hij
    · intro j hj
      have hjlt : j < n+3 := mem_range.mp (mem_filter.mp hj).1
      have hval : (j : ZMod (n+3)).val = j := ZMod.val_natCast_of_lt hjlt
      refine ⟨(j : ZMod (n+3)), mem_filter.mpr ⟨mem_univ _, ?_⟩, hval⟩
      simpa only [hval] using (mem_filter.mp hj).2
  rw [Nlt, cycleGraph_spec (n+3) hb, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_apply, cycleCosine_lt_neg_one_iff]
  rw [hcast]
  simpa only [Finset.card_def, Finset.filter_val] using hcount.symm
#print axioms Paper7PruningSpectrum.cyclicNegative_eq_Nlt

end Paper7PruningSpectrum
