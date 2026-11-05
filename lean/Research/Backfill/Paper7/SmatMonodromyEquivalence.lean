import Research.Backfill.Paper7.CyclicTransferEquivalence
import Research.Backfill.Paper7.Lemma22ExceptionalOffsets
import Research.Backfill.Paper7.Lemma22MonodromyClass

/-! Genuine Smat kernel and full ordinary-multiplicity clause of the original
Lemma22. Exact successful and uncompiled dependency versions are pinned in the
manifest; this candidate itself has not been compiled. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Periodic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem cyc_mulVec_entry (b : ℕ) (hb : 3 ≤ b) (y : Fin b → ℝ) (k : Fin b) :
    (Cyc b *ᵥ y) k = y (prv b k) + y (nxt b k) := by
  classical
  simp only [Cyc, Matrix.mulVec_apply_eq_sum,
    Paper7Lemma22.cycle_adjacency_entry b hb, add_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib]
  simp
#print axioms Paper7Lemma22Periodic.cyc_mulVec_entry

theorem smat_mulVec_entry (b : ℕ) (p q : Fin b → ℕ) (m : ℝ)
    (hb : 3 ≤ b) (y : Fin b → ℝ) (k : Fin b) :
    (Smat b p q m *ᵥ y) k =
      y (prv b k) + y (nxt b k) - (m - fk b p q m k) * y k := by
  classical
  rw [Smat, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  change (Cyc b *ᵥ y) k - m * y k + (Matrix.diagonal (fk b p q m) *ᵥ y) k = _
  rw [cyc_mulVec_entry b hb y k, Matrix.mulVec_diagonal]
  ring
#print axioms Paper7Lemma22Periodic.smat_mulVec_entry

theorem mem_ker_smat_iff (b : ℕ) (p q : Fin b → ℕ) (m : ℝ)
    (hb : 3 ≤ b) (y : Fin b → ℝ) :
    y ∈ LinearMap.ker (Matrix.toLin' (Smat b p q m)) ↔
      ∀ k, y (prv b k) + y (nxt b k) = (m - fk b p q m k) * y k := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro h k
    have hk := congrFun h k
    change (Smat b p q m *ᵥ y) k = 0 at hk
    rw [smat_mulVec_entry b p q m hb y k] at hk
    exact sub_eq_zero.mp hk
  · intro h
    funext k
    change (Smat b p q m *ᵥ y) k = 0
    rw [smat_mulVec_entry b p q m hb y k]
    exact sub_eq_zero.mpr (h k)
#print axioms Paper7Lemma22Periodic.mem_ker_smat_iff

def smatKernelEquivCycle (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) (hb : 3 ≤ b) :
    LinearMap.ker (Matrix.toLin' (Smat b p q m)) ≃ₗ[ℝ]
      cyclicSpace b (fun k => m - fk b p q m k) := by
  have he : LinearMap.ker (Matrix.toLin' (Smat b p q m)) =
      cyclicSpace b (fun k => m - fk b p q m k) := by
    apply Submodule.ext
    intro y
    exact mem_ker_smat_iff b p q m hb y
  exact LinearEquiv.ofEq _ _ he
#print axioms Paper7Lemma22Periodic.smatKernelEquivCycle

def smatKernelEquivMono (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) (hb : 3 ≤ b) :
    LinearMap.ker (Matrix.toLin' (Smat b p q m)) ≃ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (Mono b p q m - 1)) :=
  (smatKernelEquivCycle b p q m hb).trans (cycleEquivMono b hb p q m)
#print axioms Paper7Lemma22Periodic.smatKernelEquivMono

theorem ordinary_multiplicity_monodromy (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (m : ℝ) (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    mult (SG b p q) m =
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Mono b p q m - 1))) := by
  calc
    mult (SG b p q) m = matrixNullity (Smat b p q m) :=
      Paper7Lemma22.ordinary_mult_eq_smat_nullity b p q hb m hmn hm0 hm1
    _ = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Mono b p q m - 1))) :=
      (smatKernelEquivMono b p q m hb).finrank_eq
#print axioms Paper7Lemma22Periodic.ordinary_multiplicity_monodromy

/-- All four statements of the ordinary real-parameter clause; not a check of
Lemma22, whose zero and exceptional gap clauses are outside this module. -/
theorem lemma22_ordinary_clause (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    ∀ m : ℝ, m ≠ -1 → m ≠ 0 → m ≠ 1 →
      mult (SG b p q) m = Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (Mono b p q m - 1))) ∧
      mult (SG b p q) m ≤ 2 ∧
      (mult (SG b p q) m = 2 ↔ Mono b p q m = 1) ∧
      (mult (SG b p q) m = 1 ↔ Mono b p q m ≠ 1 ∧ (Mono b p q m).trace = 2) := by
  intro m hmn hm0 hm1
  have hm := ordinary_multiplicity_monodromy b p q hb m hmn hm0 hm1
  have hc := Paper7Lemma22.monodromy_kernel_classification b p q m
  change mult (SG b p q) m = matrixNullity (Mono b p q m - 1) at hm
  change mult (SG b p q) m = matrixNullity (Mono b p q m - 1) ∧ _
  rw [hm]
  exact ⟨rfl, hc⟩
#print axioms Paper7Lemma22Periodic.lemma22_ordinary_clause

end Paper7Lemma22Periodic
