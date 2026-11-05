import Research.Backfill.Paper7.CyclicTransferEquivalence

/-! The Wmat row equations and the empty-Q part of Lemma22.
The imported periodic equivalence has Root's actual development receipt. This
module is an uncompiled source candidate and does not establish full Lemma22. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps

open BackfillPaper7.Challenge
open Paper7Lemma22Periodic

/-- The actual row action, including the constrained rows in Kq. -/
theorem wmat_mulVec_entry (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) (k : Fin b) :
    (Wmat b p q ε *ᵥ y) k =
      if 0 < q k then y k
      else y (prv b k) + y (nxt b k) - ε * (1 - (p k : ℝ)) * y k := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  by_cases hq : 0 < q k
  · simp [Wmat, hq, ite_mul]
  · simp [Wmat, hq, sub_mul, add_mul, ite_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
#print axioms Paper7Lemma22Gaps.wmat_mulVec_entry

/-- Kernel membership is exactly the defining constrained recurrence. -/
theorem mem_ker_Wmat_iff (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) :
    y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) ↔
      ∀ k, if 0 < q k then y k = 0
        else y (prv b k) + y (nxt b k) = ε * (1 - (p k : ℝ)) * y k := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro h k
    have hk := congrFun h k
    change (Wmat b p q ε *ᵥ y) k = 0 at hk
    rw [wmat_mulVec_entry b p q ε y k] at hk
    by_cases hq : 0 < q k
    · simpa only [hq, ite_true] using hk
    · simpa only [hq, ite_false, sub_eq_zero] using hk
  · intro h
    funext k
    change (Wmat b p q ε *ᵥ y) k = 0
    rw [wmat_mulVec_entry b p q ε y k]
    have hk := h k
    by_cases hq : 0 < q k
    · simpa only [hq, ite_true] using hk
    · simpa only [hq, ite_false, sub_eq_zero] using hk
#print axioms Paper7Lemma22Gaps.mem_ker_Wmat_iff

theorem not_pos_q_of_empty (b : ℕ) (q : Fin b → ℕ)
    (hK : Kq b q = ∅) (k : Fin b) : ¬ 0 < q k := by
  intro hq
  have hk : k ∈ Kq b q := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hq⟩
  rw [hK] at hk
  exact Finset.notMem_empty k hk
#print axioms Paper7Lemma22Gaps.not_pos_q_of_empty

theorem mem_ker_Wmat_iff_of_empty (b : ℕ) (p q : Fin b → ℕ)
    (ε : ℝ) (hK : Kq b q = ∅) (y : Fin b → ℝ) :
    y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) ↔
      ∀ k, y (prv b k) + y (nxt b k) = ε * (1 - (p k : ℝ)) * y k := by
  rw [mem_ker_Wmat_iff]
  simp only [not_pos_q_of_empty b q hK, ite_false]
#print axioms Paper7Lemma22Gaps.mem_ker_Wmat_iff_of_empty

def wmatKernelEquivCycleOfEmpty (b : ℕ) (p q : Fin b → ℕ)
    (ε : ℝ) (hK : Kq b q = ∅) :
    LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) ≃ₗ[ℝ]
      cyclicSpace b (fun k => ε * (1 - (p k : ℝ))) := by
  have he : LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) =
      cyclicSpace b (fun k => ε * (1 - (p k : ℝ))) := by
    apply Submodule.ext
    intro y
    exact mem_ker_Wmat_iff_of_empty b p q ε hK y
  exact LinearEquiv.ofEq _ _ he
#print axioms Paper7Lemma22Gaps.wmatKernelEquivCycleOfEmpty

def wmatKernelEquivFixedOfEmpty (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (ε : ℝ) (hK : Kq b q = ∅) :
    LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) ≃ₗ[ℝ]
      fixedSpace b (fun k => ε * (1 - (p k : ℝ))) :=
  (wmatKernelEquivCycleOfEmpty b p q ε hK).trans
    (cycleEquivFixed b hb (fun k => ε * (1 - (p k : ℝ))))
#print axioms Paper7Lemma22Gaps.wmatKernelEquivFixedOfEmpty

/-- The empty-support bound holds for every real ε. -/
theorem deltaE_empty_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (hK : Kq b q = ∅) : deltaE b p q ε ≤ 2 := by
  calc
    deltaE b p q ε =
        Module.finrank ℝ (fixedSpace b (fun k => ε * (1 - (p k : ℝ)))) :=
      (wmatKernelEquivFixedOfEmpty b p q hb ε hK).finrank_eq
    _ ≤ 2 := by
      simpa only [Module.finrank_fin_fun] using
        (fixedSpace b (fun k => ε * (1 - (p k : ℝ)))).finrank_le
#print axioms Paper7Lemma22Gaps.deltaE_empty_bound

/-- The original exceptional-parameter empty-Q branch, without a full Lemma22 check. -/
theorem lemma22_empty_q_clause (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → Kq b q = ∅ → deltaE b p q ε ≤ 2 := by
  intro ε _ hK
  exact deltaE_empty_bound b p q hb ε hK
#print axioms Paper7Lemma22Gaps.lemma22_empty_q_clause

end Paper7Lemma22Gaps
