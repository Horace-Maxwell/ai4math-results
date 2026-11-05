import Research.Backfill.Paper7.LegacyEnumeration
import Research.Backfill.Paper7.CycleDihedralExact

/-! Source-only candidate. The finite orbit uses the exact frozen IsDihedral
predicate, whose rotations and reflections are genuine circle automorphisms. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningCanonical
open Finset SimpleGraph BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

theorem dihedral_id (b : ℕ) : IsDihedral b (id : Fin b → Fin b) := by
  refine ⟨0, Or.inl ?_⟩
  intro k
  simp only [id_eq, Nat.add_zero, Nat.mod_eq_of_lt k.isLt]
#print axioms Paper7PruningCanonical.dihedral_id

theorem dihedral_comp (b : ℕ) (hb : 3 ≤ b) (σ τ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (hτ : IsDihedral b τ) : IsDihedral b (σ ∘ τ) := by
  obtain ⟨e, he⟩ := Paper7Setup.cycle_iso_of_isDihedral b hb σ hσ
  obtain ⟨f, hf⟩ := Paper7Setup.cycle_iso_of_isDihedral b hb τ hτ
  have h := Paper7Setup.cycle_iso_isDihedral b hb (f.trans e)
  have heq : (fun k => (f.trans e) k) = σ ∘ τ := by
    funext k
    change e (f k) = σ (τ k)
    rw [he, hf]
  exact heq ▸ h
#print axioms Paper7PruningCanonical.dihedral_comp

theorem dihedral_bijective (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) : Function.Bijective σ := by
  obtain ⟨e, he⟩ := Paper7Setup.cycle_iso_of_isDihedral b hb σ hσ
  have heq : (fun k => e k) = σ := funext he
  exact heq ▸ e.bijective
#print axioms Paper7PruningCanonical.dihedral_bijective

theorem dihedral_inverse (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) : ∃ τ : Fin b → Fin b, IsDihedral b τ ∧
      σ ∘ τ = id ∧ τ ∘ σ = id := by
  obtain ⟨e, he⟩ := Paper7Setup.cycle_iso_of_isDihedral b hb σ hσ
  refine ⟨e.symm, Paper7Setup.cycle_iso_isDihedral b hb e.symm, ?_, ?_⟩
  · funext k
    change σ (e.symm k) = k
    rw [← he]
    exact e.apply_symm_apply k
  · funext k
    change e.symm (σ k) = k
    rw [← he]
    exact e.symm_apply_apply k
#print axioms Paper7PruningCanonical.dihedral_inverse

theorem reindex_comp {b : ℕ} (σ τ : Fin b → Fin b) (x : PQ b) :
    reindex τ (reindex σ x) = reindex (σ ∘ τ) x := rfl
#print axioms Paper7PruningCanonical.reindex_comp

theorem reindex_id {b : ℕ} (x : PQ b) : reindex id x = x := by
  cases x
  rfl
#print axioms Paper7PruningCanonical.reindex_id

def dihedralFunctions (b : ℕ) : Finset (Fin b → Fin b) :=
  univ.filter (IsDihedral b)
#print axioms Paper7PruningCanonical.dihedralFunctions

theorem mem_dihedralFunctions (b : ℕ) (σ : Fin b → Fin b) :
    σ ∈ dihedralFunctions b ↔ IsDihedral b σ := by
  simp only [dihedralFunctions, mem_filter, mem_univ, true_and]
#print axioms Paper7PruningCanonical.mem_dihedralFunctions

theorem dihedralFunctions_nonempty (b : ℕ) : (dihedralFunctions b).Nonempty :=
  ⟨id, (mem_dihedralFunctions b id).mpr (dihedral_id b)⟩
#print axioms Paper7PruningCanonical.dihedralFunctions_nonempty

/-- A first-coordinate rotation exists at every root; no choice of a preferred
root is built into the frozen graph. -/
theorem dihedral_rotation_to (b : ℕ) (hb : 0 < b) (i j : Fin b) (hj : j.val = 0) :
    ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ σ j = i := by
  let σ : Fin b → Fin b := fun k => ⟨(k.val + i.val) % b, Nat.mod_lt _ hb⟩
  refine ⟨σ, ⟨i.val, Or.inl (fun _ => rfl)⟩, ?_⟩
  apply Fin.ext
  change (j.val + i.val) % b = i.val
  simp only [hj, Nat.zero_add, Nat.mod_eq_of_lt i.isLt]
#print axioms Paper7PruningCanonical.dihedral_rotation_to

end Paper7PruningCanonical
