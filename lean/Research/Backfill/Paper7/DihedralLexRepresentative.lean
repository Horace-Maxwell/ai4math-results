import Research.Backfill.Paper7.DihedralOrbitBasics

set_option autoImplicit false
noncomputable section
namespace Paper7PruningCanonical
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

/-- Translate the actual Mathlib finite-function dictionary order into the
frozen all-equal-prefixes formulation; keys need not be injective. -/
theorem lexLE_of_toLex_le {b : ℕ} (key : ℕ → ℕ → ℕ) (x y : PQ b)
    (h : toLex (fun i => key (x.1 i) (x.2 i)) ≤
      toLex (fun i => key (y.1 i) (y.2 i))) : LexLE key x y := by
  intro i hi
  by_contra hnot
  apply not_lt_of_ge h
  change Pi.Lex (· < ·) (· < ·)
    (fun j => key (y.1 j) (y.2 j)) (fun j => key (x.1 j) (x.2 j))
  exact ⟨i, fun j hj => (hi j hj).symm, Nat.lt_of_not_ge hnot⟩
#print axioms Paper7PruningCanonical.lexLE_of_toLex_le

/-- Maxima and minima are taken over all actual dihedral functions, not over a
list of claimed representatives. Composition closes the same finite orbit. -/
theorem exists_canonical_reindex (b : ℕ) (hb : 3 ≤ b) (key : ℕ → ℕ → ℕ)
    (greatest : Bool) (x : PQ b) : ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ Canonical key greatest b (reindex σ x) := by
  let f : (Fin b → Fin b) → Lex (Fin b → ℕ) :=
    fun σ => toLex (fun i => key ((reindex σ x).1 i) ((reindex σ x).2 i))
  cases greatest with
  | false =>
    obtain ⟨σ, hσ, hmin⟩ :=
      Finset.exists_min_image (dihedralFunctions b) f (dihedralFunctions_nonempty b)
    have hσ' := (mem_dihedralFunctions b σ).mp hσ
    refine ⟨σ, hσ', ?_⟩
    intro τ hτ
    change LexLE key (reindex σ x) (reindex τ (reindex σ x))
    apply lexLE_of_toLex_le
    simpa only [f, reindex_comp] using
      hmin (σ ∘ τ) ((mem_dihedralFunctions b _).mpr (dihedral_comp b hb σ τ hσ' hτ))
  | true =>
    obtain ⟨σ, hσ, hmax⟩ :=
      Finset.exists_max_image (dihedralFunctions b) f (dihedralFunctions_nonempty b)
    have hσ' := (mem_dihedralFunctions b σ).mp hσ
    refine ⟨σ, hσ', ?_⟩
    intro τ hτ
    change LexLE key (reindex τ (reindex σ x)) (reindex σ x)
    apply lexLE_of_toLex_le
    simpa only [f, reindex_comp] using
      hmax (σ ∘ τ) ((mem_dihedralFunctions b _).mpr (dihedral_comp b hb σ τ hσ' hτ))
#print axioms Paper7PruningCanonical.exists_canonical_reindex

theorem greatest_canonical_rotation (b : ℕ) (hb : 0 < b)
    (key : ℕ → ℕ → ℕ) (x : PQ b) (hx : Canonical key true b x) :
    RotationRule key b x := by
  intro i j hj
  obtain ⟨σ, hσ, hσj⟩ := dihedral_rotation_to b hb i j hj
  have h := hx σ hσ
  change LexLE key (reindex σ x) x at h
  have hfirst := h j (fun k hk => False.elim (by omega))
  simpa only [reindex, Function.comp_apply, hσj] using hfirst
#print axioms Paper7PruningCanonical.greatest_canonical_rotation

theorem exists_rotated_maximum (b : ℕ) (hb : 3 ≤ b)
    (key : ℕ → ℕ → ℕ) (x : PQ b) : ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ RotationRule key b (reindex σ x) := by
  obtain ⟨σ, hσ, hcan⟩ := exists_canonical_reindex b hb key true x
  exact ⟨σ, hσ, greatest_canonical_rotation b (by omega) key _ hcan⟩
#print axioms Paper7PruningCanonical.exists_rotated_maximum

end Paper7PruningCanonical
