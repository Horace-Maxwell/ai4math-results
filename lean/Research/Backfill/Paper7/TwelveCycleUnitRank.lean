import Research.Backfill.Paper7.MainCycleQzeroReduction
import Research.Backfill.Paper7.Lemma24
import Research.Backfill.Paper7.SmatMonodromyEquivalence

/-! Source-only sharp exceptional-root data for a twelve-cycle below 43
vertices. All spectral and support conditions here are conclusions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem qzero_unit_multiplicity_transfer (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p (fun _ => 0)) 1 = matrixNullity (Mono b p (fun _ => 0) 1-1) := by
  have hK : Kq b (fun _ => 0) = ∅ := by simp [Kq]
  have hoff := ((Paper7Lemma22.check_Lemma22 b p (fun _ => 0) hb).2.2.1 1 (Or.inl rfl)).1
  have hm : mult (SG b p (fun _ => 0)) 1 = deltaE b p (fun _ => 0) 1 := by
    simpa [hK] using hoff
  have hk : LinearMap.ker (Matrix.toLin' (Wmat b p (fun _ => 0) 1)) =
      LinearMap.ker (Matrix.toLin' (Smat b p (fun _ => 0) 1)) := by
    apply Submodule.ext
    intro y
    rw [Paper7Lemma22Gaps.mem_ker_Wmat_iff_of_empty b p (fun _ => 0) 1 hK y,
      Paper7Lemma22Periodic.mem_ker_smat_iff b p (fun _ => 0) 1 hb y]
    simp [fk]
  calc
    _ = deltaE b p (fun _ => 0) 1 := hm
    _ = matrixNullity (Smat b p (fun _ => 0) 1) := by
      change Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Wmat b p (fun _ => 0) 1))) = _
      rw [hk]
      rfl
    _ = _ := (Paper7Lemma22Periodic.smatKernelEquivMono b p (fun _ => 0) 1 hb).finrank_eq
#print axioms Paper7MainReduction.qzero_unit_multiplicity_transfer

theorem qzero_unit_transfer_identity (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b)
    (hm : mult (SG b p (fun _ => 0)) 1 = 2) : Mono b p (fun _ => 0) 1 = 1 := by
  have hk := qzero_unit_multiplicity_transfer b p hb
  have hc := Paper7Lemma22.monodromy_kernel_classification b p (fun _ => 0) 1
  exact hc.2.1.mp (by omega)
#print axioms Paper7MainReduction.qzero_unit_transfer_identity

theorem qzero_unit_multiplicity_le_two (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p (fun _ => 0)) 1 ≤ 2 := by
  rw [qzero_unit_multiplicity_transfer b p hb]
  exact (Paper7Lemma22.monodromy_kernel_classification b p (fun _ => 0) 1).1
#print axioms Paper7MainReduction.qzero_unit_multiplicity_le_two

theorem qzero_positive_rank_balance (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b)
    (he : Even b) (hG : IsIntegralGraph (SG b p (fun _ => 0))) :
    b+(Kp b p).card = 2*(Bplus (SG b p (fun _ => 0))).card+
      2*mult (SG b p (fun _ => 0)) 1+delta0 b p := by
  have hzero := (Paper7Lemma22.check_Lemma22 b p (fun _ => 0) hb).2.1
  have hs := Paper7Admissible.lemma24_counting_even b p (fun _ => 0) hb hG he
  have hc := Paper7Counting.symmetric_spectrum_card (SG b p (fun _ => 0)) hG hs.1
  change order b (pq b p (fun _ => 0)) = _ at hc
  rw [Paper7Setup.sg_order,← hs.1 1] at hc
  simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero] at hc
  omega
#print axioms Paper7MainReduction.qzero_positive_rank_balance

theorem twelve_qzero_unit_rank (p : Fin 12 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 12 p (fun _ => 0) ≤ 42) (hG : IsIntegralGraph (SG 12 p (fun _ => 0))) :
    (Bplus (SG 12 p (fun _ => 0))).card = 4 ∧
      mult (SG 12 p (fun _ => 0)) 1 = 2 ∧ delta0 12 p = (Kp 12 p).card := by
  have hK : (Kp 12 p).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 12 p (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hd := Paper7Rank.delta0_le_card_of_nonempty 12 p hK
  have hr := qzero_positive_rank_balance 12 p (by decide) (by decide) hG
  have hu := qzero_unit_multiplicity_le_two 12 p (by decide)
  have hsmall := Paper7Admissible.lemma24_small_even_counts 12 p (fun _ => 0)
    (by decide) hG (by decide)
  obtain ⟨hcard,hfive⟩ := hsmall.2 hn
  have hn5 : (Bplus (SG 12 p (fun _ => 0))).card ≠ 5 := by
    intro heq
    have hB := hfive heq
    have hS : S2 (SG 12 p (fun _ => 0)) = 42 := by norm_num [S2,hB]
    have hs := Paper7Admissible.lemma24_counting_even 12 p (fun _ => 0)
      (by decide) hG (by decide)
    have hnR : (nOf 12 p (fun _ => 0) : ℝ) ≤ 42 := by exact_mod_cast hn
    have hmR : (mult (SG 12 p (fun _ => 0)) 1 : ℝ) = 0 := by
      have hmn : (0 : ℝ) ≤ mult (SG 12 p (fun _ => 0)) 1 := Nat.cast_nonneg _
      rw [hS] at hs
      linarith only [hs.2.1,hnR,hmn]
    have hm : mult (SG 12 p (fun _ => 0)) 1 = 0 := by exact_mod_cast hmR
    omega
  exact ⟨by omega,by omega,by omega⟩
#print axioms Paper7MainReduction.twelve_qzero_unit_rank

end Paper7MainReduction
