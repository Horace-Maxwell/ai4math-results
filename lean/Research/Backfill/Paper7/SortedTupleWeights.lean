import Research.Backfill.Paper7.SortedBoundedTuples

/-! Source-only candidate. The weight is the number of distinct ordered rows
in the genuine permutation orbit. It is not a count of permutation witnesses. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SortedRows
open Paper7Budget
open scoped BigOperators Classical

def orbitFinset {n B : ℕ} (x : BoundedTuple n B) : Finset (BoundedTuple n B) :=
  Finset.univ.image (fun e : Equiv.Perm (Fin n) => permute e x)
#print axioms Paper7SortedRows.orbitFinset

theorem mem_orbitFinset_iff {n B : ℕ} (x y : BoundedTuple n B) :
    y ∈ orbitFinset x ↔ ∃ e : Equiv.Perm (Fin n), y = permute e x := by
  constructor
  · intro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact ⟨e, he.symm⟩
  · rintro ⟨e, rfl⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
#print axioms Paper7SortedRows.mem_orbitFinset_iff

theorem mem_orbitFinset_iff_mem_orbit {n B : ℕ} (x y : BoundedTuple n B) :
    y ∈ orbitFinset x ↔ y ∈ MulAction.orbit (Equiv.Perm (Fin n)) x := by
  rw [mem_orbitFinset_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.symm, rfl⟩
  · rintro ⟨e, he⟩
    exact ⟨e.symm, he.symm⟩
#print axioms Paper7SortedRows.mem_orbitFinset_iff_mem_orbit

def orbitWeight {n B : ℕ} (x : BoundedTuple n B) : ℕ := (orbitFinset x).card
#print axioms Paper7SortedRows.orbitWeight

theorem orbitWeight_pos {n B : ℕ} (x : BoundedTuple n B) : 0 < orbitWeight x := by
  apply Finset.card_pos.mpr
  refine ⟨x, (mem_orbitFinset_iff x x).mpr ?_⟩
  exact ⟨Equiv.refl _, (permute_refl x).symm⟩
#print axioms Paper7SortedRows.orbitWeight_pos

theorem orbitWeight_le_factorial {n B : ℕ} (x : BoundedTuple n B) :
    orbitWeight x ≤ n.factorial := by
  calc
    orbitWeight x ≤ Fintype.card (Equiv.Perm (Fin n)) :=
      (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
#print axioms Paper7SortedRows.orbitWeight_le_factorial

def orbitFinsetEquivOrbit {n B : ℕ} (x : BoundedTuple n B) :
    ↥(orbitFinset x) ≃ ↥(MulAction.orbit (Equiv.Perm (Fin n)) x) :=
  Equiv.subtypeEquivRight (fun y => mem_orbitFinset_iff_mem_orbit x y)
#print axioms Paper7SortedRows.orbitFinsetEquivOrbit

theorem orbitWeight_eq_card_orbit {n B : ℕ} (x : BoundedTuple n B) :
    orbitWeight x = Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) x) := by
  exact (Fintype.card_coe (orbitFinset x)).symm.trans
    (Fintype.card_congr (orbitFinsetEquivOrbit x))
#print axioms Paper7SortedRows.orbitWeight_eq_card_orbit

/-- Exact orbit-stabilizer weight, with no freeness assumption. -/
theorem orbitWeight_mul_stabilizer {n B : ℕ} (x : BoundedTuple n B) :
    orbitWeight x * Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) x) =
      n.factorial := by
  rw [orbitWeight_eq_card_orbit,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group,
    Fintype.card_perm, Fintype.card_fin]
#print axioms Paper7SortedRows.orbitWeight_mul_stabilizer

/-- Inversion identifies the left-action stabilizer with permutations that
preserve the tuple by direct precomposition. -/
def stabilizerEquivPreserving {n B : ℕ} (x : BoundedTuple n B) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) x ≃
      {e : Equiv.Perm (Fin n) // x.val ∘ e = x.val} where
  toFun g := ⟨g.val.symm, by
    exact congrArg (fun y : BoundedTuple n B => y.val)
      (MulAction.mem_stabilizer_iff.mp g.property)⟩
  invFun e := ⟨e.val.symm, by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subtype.ext
    exact e.property⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl
#print axioms Paper7SortedRows.stabilizerEquivPreserving

theorem stabilizer_card_eq_multiplicities {n B : ℕ} (x : BoundedTuple n B) :
    Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) x) =
      ∏ v ∈ Finset.univ.image x.val, (Fintype.card {i : Fin n // x.val i = v}).factorial := by
  exact (Fintype.card_congr (stabilizerEquivPreserving x)).trans
    (DomMulAct.stabilizer_card' x.val)
#print axioms Paper7SortedRows.stabilizer_card_eq_multiplicities

/-- Repeated values reduce the orbit size by the product of their
multiplicity factorials; no list of equality patterns is assumed. -/
theorem orbitWeight_mul_multiplicities {n B : ℕ} (x : BoundedTuple n B) :
    orbitWeight x *
      (∏ v ∈ Finset.univ.image x.val, (Fintype.card {i : Fin n // x.val i = v}).factorial) =
      n.factorial := by
  rw [← stabilizer_card_eq_multiplicities]
  exact orbitWeight_mul_stabilizer x
#print axioms Paper7SortedRows.orbitWeight_mul_multiplicities

theorem sort_eq_sorted_iff_mem {n B : ℕ} (x : BoundedTuple n B)
    (r : SortedTuple n B) : sortBounded x = r ↔ x ∈ orbitFinset r.val := by
  rw [mem_orbitFinset_iff, ← sort_eq_iff_permutation, sortBounded_of_sorted]
  exact eq_comm
#print axioms Paper7SortedRows.sort_eq_sorted_iff_mem

def sortedFibreEquivOrbit {n B : ℕ} (r : SortedTuple n B) :
    {x : BoundedTuple n B // sortBounded x = r} ≃ ↥(orbitFinset r.val) :=
  Equiv.subtypeEquivRight (fun x => sort_eq_sorted_iff_mem x r)
#print axioms Paper7SortedRows.sortedFibreEquivOrbit

theorem sorted_fibre_card {n B : ℕ} (r : SortedTuple n B) :
    Fintype.card {x : BoundedTuple n B // sortBounded x = r} = orbitWeight r.val := by
  exact (Fintype.card_congr (sortedFibreEquivOrbit r)).trans
    (Fintype.card_coe (orbitFinset r.val))
#print axioms Paper7SortedRows.sorted_fibre_card

def sortedSigmaEquiv {n B : ℕ} : BoundedTuple n B ≃
    Σ r : SortedTuple n B, {x : BoundedTuple n B // sortBounded x = r} where
  toFun x := ⟨sortBounded x, ⟨x, rfl⟩⟩
  invFun s := s.2.val
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨r, x, h⟩
    cases h
    rfl
#print axioms Paper7SortedRows.sortedSigmaEquiv

/-- Full-domain sum, partitioned into its uniquely sorted fibres. The only
generic premise is permutation invariance, discharged for B1 in the next file. -/
theorem sum_sorted_weighted {n B : ℕ} (f : BoundedTuple n B → ℕ)
    (hf : ∀ (e : Equiv.Perm (Fin n)) (x : BoundedTuple n B), f (permute e x) = f x) :
    (∑ x : BoundedTuple n B, f x) =
      ∑ r : SortedTuple n B, orbitWeight r.val * f r.val := by
  calc
    (∑ x : BoundedTuple n B, f x) =
        ∑ s : Σ r : SortedTuple n B, {x : BoundedTuple n B // sortBounded x = r},
          f s.2.val :=
      ((sortedSigmaEquiv (n := n) (B := B)).symm.bijective.sum_comp f).symm
    _ = ∑ r : SortedTuple n B,
        ∑ x : {x : BoundedTuple n B // sortBounded x = r}, f x.val :=
      Fintype.sum_sigma _
    _ = ∑ r : SortedTuple n B, orbitWeight r.val * f r.val := by
      apply Finset.sum_congr rfl
      intro r _
      have hconst : ∀ x : {x : BoundedTuple n B // sortBounded x = r},
          f x.val = f r.val := by
        intro x
        obtain ⟨e, he⟩ := (mem_orbitFinset_iff r.val x.val).mp
          ((sort_eq_sorted_iff_mem x.val r).mp x.property)
        rw [he]
        exact hf e r.val
      calc
        (∑ x : {x : BoundedTuple n B // sortBounded x = r}, f x.val) =
            ∑ _x : {x : BoundedTuple n B // sortBounded x = r}, f r.val :=
          Finset.sum_congr rfl (fun x _ => hconst x)
        _ = Fintype.card {x : BoundedTuple n B // sortBounded x = r} * f r.val := by
          exact Finset.sum_const_nat (fun _ _ => rfl)
        _ = orbitWeight r.val * f r.val := by rw [sorted_fibre_card]
#print axioms Paper7SortedRows.sum_sorted_weighted

end Paper7SortedRows
