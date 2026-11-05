import Research.Backfill.Paper7.DihedralBudgetIntegral

/-! Exactly the relabeling guards of each frozen Stage. Remaining stage guards
must be proved afresh on the integral relabeled graph; prefix expressions are
not asserted to be invariant under a dihedral permutation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningCanonical
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

/-- A single key and direction sufficient for each version's actual guards. -/
def versionKey : SearchVersion → ℕ → ℕ → ℕ
  | .a4 | .a5 | .a6 _ | .b1 | .b2 | .b3 => key1000
  | .c _ | .c2 _ _ => keySupport
  | .d1 _ => key64
  | .d2 _ _ w | .d3 _ _ w _ => if w then keyWeight else key64
#print axioms Paper7PruningCanonical.versionKey

def versionGreatest : SearchVersion → Bool
  | .a4 | .a5 | .a6 _ | .b3 => true
  | .b1 | .b2 | .c _ | .c2 _ _ | .d1 _ => false
  | .d2 _ _ w | .d3 _ _ w _ => w
#print axioms Paper7PruningCanonical.versionGreatest

def VersionCanonicalGuards (v : SearchVersion) (b : ℕ) (x : PQ b) : Prop :=
  match v with
  | .a4 | .a5 | .a6 _ => RotationRule key1000 b x
  | .b1 | .b2 => Canonical key1000 false b x
  | .b3 => Canonical key1000 true b x ∧ RotationRule key1000 b x
  | .c _ | .c2 _ _ => Canonical keySupport false b x
  | .d1 c => c = true → Canonical key64 false b x
  | .d2 c _ w | .d3 c _ w _ =>
    (c = true → Canonical (if w then keyWeight else key64) w b x) ∧
      (w = true → RotationRule (fun p q => p+2*q) b x)
#print axioms Paper7PruningCanonical.VersionCanonicalGuards

theorem version_canonical_guards (v : SearchVersion) (b N : ℕ)
    (hb : 3 ≤ b) (hN : N ≤ 49) (x : PQ b) (hx : Budget b N x)
    (hcan : Canonical (versionKey v) (versionGreatest v) b x) :
    VersionCanonicalGuards v b x := by
  cases v with
  | a4 => exact greatest_canonical_rotation b (by omega) key1000 x hcan
  | a5 => exact greatest_canonical_rotation b (by omega) key1000 x hcan
  | a6 _c => exact greatest_canonical_rotation b (by omega) key1000 x hcan
  | b1 => exact hcan
  | b2 => exact hcan
  | b3 => exact ⟨hcan, greatest_canonical_rotation b (by omega) key1000 x hcan⟩
  | c _r => exact hcan
  | c2 _r _rr => exact hcan
  | d1 _c => exact fun _ => hcan
  | d2 _c _l w =>
    refine ⟨fun _ => hcan, ?_⟩
    intro hw
    subst w
    exact weight_rotation_of_canonical b N hb hN x hx hcan
  | d3 _c _l w _np =>
    refine ⟨fun _ => hcan, ?_⟩
    intro hw
    subst w
    exact weight_rotation_of_canonical b N hb hN x hx hcan
#print axioms Paper7PruningCanonical.version_canonical_guards

/-- Original graph and budget assumptions alone provide every version's exact
canonical and rotation guards, with no assumption of stage completeness. -/
theorem exists_version_representative (v : SearchVersion) (b N : ℕ)
    (hb : 3 ≤ b) (hN : N ≤ 49) (x : PQ b) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ Budget b N (reindex σ x) ∧
      IsIntegralGraph (SG b (reindex σ x).1 (reindex σ x).2) ∧
      VersionCanonicalGuards v b (reindex σ x) := by
  obtain ⟨σ, hσ, hcan⟩ :=
    exists_canonical_reindex b hb (versionKey v) (versionGreatest v) x
  have hbudget := (reindex_budget_iff b N hb σ hσ x).mpr hx
  exact ⟨σ, hσ, hbudget, (reindex_integral_iff b hb σ hσ x).mpr hG,
    version_canonical_guards v b N hb hN _ hbudget hcan⟩
#print axioms Paper7PruningCanonical.exists_version_representative

end Paper7PruningCanonical
