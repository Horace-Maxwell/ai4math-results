import Research.Backfill.Paper1.SupplementStatements
import Research.Backfill.Paper1.GraphBridge
import Research.ICGGeneralMain

/-!
Static proof source for the proposed general EqG supplement.
No compilation or acceptance is asserted by this file.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31EqG

lemma last_entry_nonneg {p : ℝ} (hp : 1 ≤ p) (a i : ℕ) :
    0 ≤ Challenge.tEntry a p a i := by
  unfold Challenge.tEntry
  simp only [lt_self_iff_false, false_and, ite_false]
  split_ifs
  · exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
  · norm_num

lemma corner_nonneg {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (a b : ℕ) (X : ℕ → ℕ → ℝ)
    (hX : ∀ i ≤ a, ∀ j ≤ b, 0 ≤ X i j) :
    0 ≤ Mentry p q a b X a b := by
  rw [← PathAndSign.triple_eq_Mentry p q a b X a b le_rfl le_rfl]
  unfold Challenge.triple
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (last_entry_nonneg hp a i)
      (hX i (by simpa using Finset.mem_range.mp hi)
        j (by simpa using Finset.mem_range.mp hj)))
    (last_entry_nonneg hq b j)

lemma twice_norm_eq {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (a b : ℕ) (X : ℕ → ℕ → ℝ)
    (hX : ∀ i ≤ a, ∀ j ≤ b, 0 ≤ X i j) :
    2 * L1mat p q a b X = p ^ a * q ^ b +
      Challenge.Gval a b p q (fun i j => 2 * X i j - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  let Y : ℕ → ℕ → ℝ := fun i j => 2 * X i j - 1
  have hc := corner_nonneg hp hq a b X hX
  have hlin : Mentry p q a b Y a b + p ^ a * q ^ b =
      2 * Mentry p q a b X a b := by
    have hh := Mentry_lin p q a b X 2 (-1) a b
    have hy : (fun i j => 2 * X i j + -1) = Y := by
      funext i j; dsimp [Y]; ring
    rw [hy, Mentry_ones hp0 hq0 a b le_rfl le_rfl] at hh
    simp only [and_self, ite_true] at hh
    linarith
  have hterm (u v : ℕ) (hu : u ≤ a) (hv : v ≤ b) :
      |Mentry p q a b Y u v + Mentry p q a b (fun _ _ => 1) u v| =
        (if u = a ∧ v = b then Challenge.triple a b p q Y u v
          else |Challenge.triple a b p q Y u v|) +
        (if a = u ∧ b = v then p ^ a * q ^ b else 0) := by
    rw [PathAndSign.triple_eq_Mentry p q a b Y u v hu hv,
      Mentry_ones hp0 hq0 a b hu hv]
    by_cases he : u = a ∧ v = b
    · rcases he with ⟨rfl, rfl⟩
      simp only [and_self, ite_true]
      rw [abs_of_nonneg (by linarith [hlin])]
    · have he' : ¬ (a = u ∧ b = v) := by
        rintro ⟨h1, h2⟩; exact he ⟨h1.symm, h2.symm⟩
      simp only [ite_eq_right he, ite_eq_right he', add_zero]
  rw [two_L1mat]
  change (∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
      |Mentry p q a b Y u v + Mentry p q a b (fun _ _ => 1) u v|) = _
  calc
    _ = (∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        ((if u = a ∧ v = b then Challenge.triple a b p q Y u v
          else |Challenge.triple a b p q Y u v|) +
        (if a = u ∧ b = v then p ^ a * q ^ b else 0))) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact hterm u v (by simpa using Finset.mem_range.mp hu)
        (by simpa using Finset.mem_range.mp hv)
    _ = p ^ a * q ^ b + Challenge.Gval a b p q Y := by
      simp only [Finset.sum_add_distrib]
      rw [sum_corner]
      change Challenge.Gval a b p q Y + p ^ a * q ^ b = _
      ring

end Prop31EqG

theorem check_GeneralEqG : NarrowSupplement.GeneralEqG := by
  intro p q a b hp hq hpq ha hb D hD
  rw [check_Proposition6 p q a b hp hq hpq ha hb D hD,
    PathAndSign.l1Mat_triple_eq_L1mat]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  have hh := Prop31EqG.twice_norm_eq hpR hqR a b (Challenge.divMat p q D)
    (by intros; unfold Challenge.divMat; split_ifs <;> norm_num)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hh

end CodexPaper1

#print axioms CodexPaper1.check_GeneralEqG
