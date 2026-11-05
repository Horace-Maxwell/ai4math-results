import Research.Backfill.Paper7.OddPerronBoundary
import Research.Backfill.Paper7.Lemma24BasicBounds
import Research.Backfill.Paper7.PQArmCoordinates
import Research.Backfill.Paper7.SunCycleCount

set_option autoImplicit false

noncomputable section

namespace Paper7Admissible

open Matrix SimpleGraph BackfillPaper7.Challenge Paper7Cleared Paper7Reduced Paper7Inertia
open scoped Matrix

theorem sun_arm_reachable (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    (sunGraph b L).Reachable (Sum.inl k) (Sum.inr ⟨k, j, a⟩) := by
  have h : ∀ (n : ℕ) (hn : n < (L k).get j),
      (sunGraph b L).Reachable (Sum.inl k) (Sum.inr ⟨k, j, ⟨n, hn⟩⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact ((sun_root_arm_adj_iff b L k k j ⟨0, hn⟩).mpr ⟨rfl, rfl⟩).reachable
    | succ n ih =>
      intro hn
      have hn' : n < (L k).get j := by omega
      have ha : (sunGraph b L).Adj
          (Sum.inr ⟨k, j, (⟨n, hn'⟩ : Fin ((L k).get j))⟩)
          (Sum.inr ⟨k, j, (⟨n+1, hn⟩ : Fin ((L k).get j))⟩) :=
        (sun_arm_adj_iff b L k k j j ⟨n, hn'⟩ ⟨n+1, hn⟩).mpr
          ⟨rfl, rfl, Or.inl rfl⟩
      exact (ih hn').trans ha.reachable
  exact h a.val a.isLt
#print axioms Paper7Admissible.sun_arm_reachable

theorem sun_connected (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    (sunGraph b L).Connected := by
  have hc : (SimpleGraph.cycleGraph b).Connected := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n+1 := ⟨b-1, by omega⟩
    exact SimpleGraph.cycleGraph_connected
  let k₀ : Fin b := ⟨0, by omega⟩
  have hr (k : Fin b) : (sunGraph b L).Reachable (Sum.inl k₀) (Sum.inl k) :=
    SimpleGraph.Reachable.map (Paper7SunMoments.sunCycleHom b L hb) (hc k₀ k)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (sunGraph b L)).mpr
  refine ⟨Sum.inl k₀, ?_⟩
  intro v
  rcases v with k | ⟨k, j, a⟩
  · exact hr k
  · exact (hr k).trans (sun_arm_reachable b L k j a)
#print axioms Paper7Admissible.sun_connected

def sunCoreVector (b : ℕ) (L : Fin b → List ℕ) : SunV b L → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)
#print axioms Paper7Admissible.sunCoreVector

theorem sunCoreVector_norm (b : ℕ) (L : Fin b → List ℕ) :
    sunCoreVector b L ⬝ᵥ sunCoreVector b L = (b : ℝ) := by
  simp [dotProduct, sunCoreVector, Fintype.sum_sum_type]
#print axioms Paper7Admissible.sunCoreVector_norm

theorem sunCoreVector_root_row (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (k : Fin b) :
    ((sunGraph b L).adjMatrix ℝ *ᵥ sunCoreVector b L) (Sum.inl k) = 2 := by
  have h : ((sunGraph b L).adjMatrix ℝ *ᵥ sunCoreVector b L) (Sum.inl k) =
      ((SimpleGraph.cycleGraph b).adjMatrix ℝ *ᵥ (fun _ => 1)) k := by
    simp [Matrix.mulVec, dotProduct, sunCoreVector, Fintype.sum_sum_type,
      SimpleGraph.adjMatrix_apply, sun_cycle_adj_iff b L hb]
  rw [h]
  have hd : (SimpleGraph.cycleGraph b).degree k = 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n+3 := ⟨b-3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  change ((SimpleGraph.cycleGraph b).adjMatrix ℝ *ᵥ Function.const _ (1 : ℝ)) k = 2
  rw [SimpleGraph.adjMatrix_mulVec_const_apply, hd]
  norm_num
#print axioms Paper7Admissible.sunCoreVector_root_row

theorem sunCoreVector_arm_row (b : ℕ) (L : Fin b → List ℕ) (k : Fin b)
    (j : Fin (L k).length) (a : Fin ((L k).get j)) :
    ((sunGraph b L).adjMatrix ℝ *ᵥ sunCoreVector b L) (Sum.inr ⟨k, j, a⟩) =
      if a.val = 0 then 1 else 0 := by
  classical
  by_cases ha : a.val = 0 <;>
    simp [Matrix.mulVec, dotProduct, sunCoreVector, Fintype.sum_sum_type,
      SimpleGraph.adjMatrix_apply, sun_arm_root_adj_iff, ha]
#print axioms Paper7Admissible.sunCoreVector_arm_row

theorem sunCoreVector_quadratic (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    ((sunGraph b L).adjMatrix ℝ).toQuadraticForm' (sunCoreVector b L) = 2 * (b : ℝ) := by
  rw [quadratic_apply]
  simp only [dotProduct, Fintype.sum_sum_type, sunCoreVector, Sum.elim_inl,
    Sum.elim_inr, one_mul, zero_mul, Finset.sum_const_zero, add_zero]
  change (∑ k : Fin b, ((sunGraph b L).adjMatrix ℝ *ᵥ sunCoreVector b L) (Sum.inl k)) = _
  simp only [sunCoreVector_root_row b L hb, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring
#print axioms Paper7Admissible.sunCoreVector_quadratic

theorem positive_pendants_have_arm (b : ℕ) (p q : Fin b → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) :
    ∃ k : Fin b, Nonempty (Fin (pq b p q k).length) := by
  obtain ⟨k, hk⟩ : ∃ k, 0 < p k + q k := by
    by_contra! h
    have hz : ∑ k, (p k + q k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Nat.eq_zero_of_le_zero (h k)
    omega
  have hlen : 0 < (pq b p q k).length := by simpa [pq] using hk
  exact ⟨k, ⟨⟨0, hlen⟩⟩⟩
#print axioms Paper7Admissible.positive_pendants_have_arm

/-- Proper containment of the actual cycle forces a strict top bound, for all b and p,q. -/
theorem sun_top_gt_two (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hp : 0 < ∑ k, (p k + q k)) (r : ℝ)
    (hupper : ∀ x, ((SG b p q).adjMatrix ℝ).toQuadraticForm' x ≤ r * (x ⬝ᵥ x)) :
    2 < r := by
  have h := hupper (sunCoreVector b (pq b p q))
  rw [sunCoreVector_quadratic b (pq b p q) hb, sunCoreVector_norm] at h
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hr : 2 ≤ r := by nlinarith
  have hne : r ≠ 2 := by
    intro heq
    have hx : ((SG b p q).adjMatrix ℝ).toQuadraticForm' (sunCoreVector b (pq b p q)) =
        r * (sunCoreVector b (pq b p q) ⬝ᵥ sunCoreVector b (pq b p q)) := by
      rw [sunCoreVector_quadratic b (pq b p q) hb, sunCoreVector_norm, heq]
    have he := eigen_of_quadratic_equality ((SG b p q).adjMatrix ℝ)
      (Paper7Spectrum.realAdjHermitian (SG b p q)) r hupper _ hx
    obtain ⟨k, ⟨j⟩⟩ := positive_pendants_have_arm b p q hp
    have hv := congrFun he (Sum.inr ⟨k, j, armFirst b p q k j⟩)
    rw [sunCoreVector_arm_row] at hv
    simp [armFirst, sunCoreVector] at hv
  exact lt_of_le_of_ne hr (Ne.symm hne)
#print axioms Paper7Admissible.sun_top_gt_two

/-- The full original (a), including simple Perron root and strict odd-cycle lower boundary. -/
theorem lemma24_perron (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hp : 0 < ∑ k, (p k + q k)) (hG : IsIntegralGraph (SG b p q)) :
    ∃ r ∈ spec (SG b p q), mult (SG b p q) r = 1 ∧ 3 ≤ r ∧
      ∀ x ∈ spec (SG b p q), |x| ≤ r ∧ x ^ 2 ≤ 2 * (nOf b p q : ℝ) ∧
        (Odd b → -r < x) := by
  let : Nonempty (SunV b (pq b p q)) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hconn := sun_connected b (pq b p q) hb
  obtain ⟨r, hr, v, hv, hvnorm, hve, hr0, hsimp, hupper, hdom⟩ :=
    connected_perron (SG b p q) hconn
  have hr2 := sun_top_gt_two b p q hb hp r hupper
  have hr3 : 3 ≤ r := by
    obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry (SG b p q) hG r hr
    rw [hz] at hr2 ⊢
    have hz2 : (2 : ℤ) < z := by exact_mod_cast hr2
    exact_mod_cast (by omega : (3 : ℤ) ≤ z)
  refine ⟨r, hr, hsimp, hr3, ?_⟩
  intro x hx
  refine ⟨hdom x hx, lemma24_square_bound b p q hb x hx, ?_⟩
  intro hodd
  obtain ⟨i, walk, hc, hlen, hedges⟩ := Paper7SunMoments.sun_reference_cycle b (pq b p q) hb
  have ho : Odd walk.length := hlen.symm ▸ hodd
  have hnot := odd_closed_walk_excludes_negative_perron (SG b p q) hconn r hr0 v hv hve i walk ho
  have hne : x ≠ -r := by
    intro he
    exact hnot (he ▸ hx)
  exact lt_of_le_of_ne (abs_le.mp (hdom x hx)).1 (Ne.symm hne)
#print axioms Paper7Admissible.lemma24_perron

end Paper7Admissible
