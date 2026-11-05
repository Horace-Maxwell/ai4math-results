import Research.Backfill.Paper7.MomentCanonicalBridge

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
MomentCanonicalBridge and its canonical/Stage 01 dependencies remain pending.
This module has not been compiled or accepted. It proves a Burnside identity for
the actual CandB1 action. The subgroup cardinality, cycle-block descriptions and
all concrete numerical counts remain separate obligations.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningCanonical
open scoped BigOperators Classical

/-- The subgroup contains exactly the permutations satisfying the frozen predicate. -/
def dihedralSubgroup (b : ℕ) (hb : 3 ≤ b) : Subgroup (Equiv.Perm (Fin b)) where
  carrier := {σ | IsDihedral b σ}
  one_mem' := dihedral_id b
  mul_mem' := by
    intro σ τ hσ hτ
    exact dihedral_comp b hb σ τ hσ hτ
  inv_mem' := by
    intro σ hσ
    obtain ⟨τ, hτ, hστ, _hτσ⟩ := dihedral_inverse b hb σ hσ
    have heq : τ = (fun i => (σ⁻¹) i) := by
      funext i
      apply σ.injective
      have hi : σ (τ i) = i := congrFun hστ i
      exact hi.trans (σ.apply_symm_apply i).symm
    change IsDihedral b (fun i => (σ⁻¹) i)
    rw [← heq]
    exact hτ

#print axioms Paper7MomentCounts.dihedralSubgroup

instance dihedralSubgroupFintype (b : ℕ) (hb : 3 ≤ b) :
    Fintype (dihedralSubgroup b hb) := Fintype.ofFinite _

#print axioms Paper7MomentCounts.dihedralSubgroupFintype

instance momentCandidateFintype (b N : ℕ) : Fintype ↥(CandB1 b N) :=
  (candB1_finite b N).fintype

#print axioms Paper7MomentCounts.momentCandidateFintype

/-- Inverse reindexing gives a left action for the usual permutation multiplication. -/
@[instance_reducible]
def candB1DihedralAction (b N : ℕ) (hb : 3 ≤ b) :
    MulAction (dihedralSubgroup b hb) ↥(CandB1 b N) where
  smul σ x :=
    ⟨reindex (σ⁻¹ : dihedralSubgroup b hb).val x.val,
      (candB1_reindex_iff b N hb (σ⁻¹ : dihedralSubgroup b hb).val
        (σ⁻¹ : dihedralSubgroup b hb).property x.val).mpr x.property⟩
  one_smul x := by
    apply Subtype.ext
    change reindex ((1 : dihedralSubgroup b hb)⁻¹).val x.val = x.val
    simpa only [inv_one, Subgroup.coe_one, Equiv.Perm.coe_one] using reindex_id x.val
  mul_smul σ τ x := by
    apply Subtype.ext
    change reindex ((σ * τ)⁻¹ : dihedralSubgroup b hb).val x.val =
      reindex (σ⁻¹ : dihedralSubgroup b hb).val
        (reindex (τ⁻¹ : dihedralSubgroup b hb).val x.val)
    simpa only [mul_inv_rev, Subgroup.coe_mul, Equiv.Perm.coe_mul] using
      (reindex_comp (τ⁻¹ : dihedralSubgroup b hb).val
        (σ⁻¹ : dihedralSubgroup b hb).val x.val).symm

#print axioms Paper7MomentCounts.candB1DihedralAction

abbrev CandB1Orbits (b N : ℕ) (hb : 3 ≤ b) :=
  @MulAction.orbitRel.Quotient (dihedralSubgroup b hb) ↥(CandB1 b N) _
    (candB1DihedralAction b N hb)

#print axioms Paper7MomentCounts.CandB1Orbits

/-- Mathlib's orbit relation has the first argument in the second argument's orbit. -/
theorem candidate_orbitRel_iff (b N : ℕ) (hb : 3 ≤ b) (x y : ↥(CandB1 b N)) :
    @MulAction.orbitRel (dihedralSubgroup b hb) ↥(CandB1 b N) _
      (candB1DihedralAction b N hb) x y ↔
      sameDihedralOrbit b y.val x.val := by
  let : MulAction (dihedralSubgroup b hb) ↥(CandB1 b N) :=
    candB1DihedralAction b N hb
  change (∃ σ : dihedralSubgroup b hb, σ • y = x) ↔ _
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(σ⁻¹ : dihedralSubgroup b hb).val,
      (σ⁻¹ : dihedralSubgroup b hb).property, ?_⟩
    exact congrArg Subtype.val hσ
  · rintro ⟨σ, hσ, hxy⟩
    let e : Equiv.Perm (Fin b) :=
      Equiv.ofBijective σ (dihedral_bijective b hb σ hσ)
    let g : dihedralSubgroup b hb := ⟨e, hσ⟩
    refine ⟨g⁻¹, ?_⟩
    apply Subtype.ext
    change reindex ((g⁻¹)⁻¹ : dihedralSubgroup b hb).val y.val = x.val
    rw [inv_inv]
    change reindex σ y.val = x.val
    exact hxy

#print axioms Paper7MomentCounts.candidate_orbitRel_iff

def canonB1ToOrbit (b N : ℕ) (hb : 3 ≤ b) :
    ↥(canonB1 b N) → CandB1Orbits b N hb :=
  fun x => Quotient.mk'' (⟨x.val, x.property.1⟩ : ↥(CandB1 b N))

#print axioms Paper7MomentCounts.canonB1ToOrbit

theorem canonB1ToOrbit_bijective (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49) :
    Function.Bijective (canonB1ToOrbit b N hb) := by
  let : MulAction (dihedralSubgroup b hb) ↥(CandB1 b N) :=
    candB1DihedralAction b N hb
  constructor
  · intro x y h
    change (Quotient.mk'' (⟨x.val, x.property.1⟩ : ↥(CandB1 b N)) :
      CandB1Orbits b N hb) =
        Quotient.mk'' (⟨y.val, y.property.1⟩ : ↥(CandB1 b N)) at h
    have hrel : MulAction.orbitRel (dihedralSubgroup b hb) ↥(CandB1 b N)
        (⟨x.val, x.property.1⟩ : ↥(CandB1 b N))
        (⟨y.val, y.property.1⟩ : ↥(CandB1 b N)) := Quotient.exact h
    have horbit := (candidate_orbitRel_iff b N hb _ _).mp hrel
    apply Subtype.ext
    exact (canonical_eq_of_sameDihedralOrbit b hb (CandB1 b N) key1000 false
      (key1000_profile_injective_candB1 b N hN) y.property x.property horbit).symm
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    obtain ⟨y, hy, _hunique⟩ := exists_unique_canonical b hb (CandB1 b N)
      key1000 false
      (fun z hz σ hσ => (candB1_reindex_iff b N hb σ hσ z).mpr hz)
      (key1000_profile_injective_candB1 b N hN) x.val x.property
    refine ⟨⟨y, hy.1⟩, ?_⟩
    change (Quotient.mk'' (⟨y, hy.1.1⟩ : ↥(CandB1 b N)) : CandB1Orbits b N hb) =
      Quotient.mk'' x
    apply Quotient.sound
    exact (candidate_orbitRel_iff b N hb
      (⟨y, hy.1.1⟩ : ↥(CandB1 b N)) x).mpr hy.2

#print axioms Paper7MomentCounts.canonB1ToOrbit_bijective

def canonB1OrbitEquiv (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49) :
    ↥(canonB1 b N) ≃ CandB1Orbits b N hb :=
  Equiv.ofBijective (canonB1ToOrbit b N hb) (canonB1ToOrbit_bijective b N hb hN)

#print axioms Paper7MomentCounts.canonB1OrbitEquiv

/-- Burnside's multiplication identity for the actual original candidate set. -/
theorem candB1_burnside (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49) :
    (∑ σ : dihedralSubgroup b hb,
      Fintype.card (@MulAction.fixedBy (dihedralSubgroup b hb) ↥(CandB1 b N) _
        (candB1DihedralAction b N hb) σ)) =
      (canonB1 b N).ncard * Fintype.card (dihedralSubgroup b hb) := by
  let : MulAction (dihedralSubgroup b hb) ↥(CandB1 b N) :=
    candB1DihedralAction b N hb
  let : Fintype (CandB1Orbits b N hb) := Fintype.ofFinite _
  let : Fintype ↥(canonB1 b N) := (canonB1_finite b N).fintype
  have hc : Fintype.card (CandB1Orbits b N hb) = (canonB1 b N).ncard := by
    calc
      Fintype.card (CandB1Orbits b N hb) = Fintype.card ↥(canonB1 b N) :=
        (Fintype.card_congr (canonB1OrbitEquiv b N hb hN)).symm
      _ = (canonB1 b N).ncard := Set.fintypeCard_eq_ncard _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (dihedralSubgroup b hb) ↥(CandB1 b N)
  rw [hc] at h
  exact h

#print axioms Paper7MomentCounts.candB1_burnside

end Paper7MomentCounts
