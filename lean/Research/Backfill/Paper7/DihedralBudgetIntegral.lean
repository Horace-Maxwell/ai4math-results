import Research.Backfill.Paper7.DihedralLexRepresentative

set_option autoImplicit false
noncomputable section
namespace Paper7PruningCanonical
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

theorem reindex_sums (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) :
    pSum (reindex σ x) = pSum x ∧ qSum (reindex σ x) = qSum x := by
  have hbij := dihedral_bijective b hb σ hσ
  exact ⟨hbij.sum_comp x.1, hbij.sum_comp x.2⟩
#print axioms Paper7PruningCanonical.reindex_sums

theorem reindex_weight (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) : weight (reindex σ x) = weight x := by
  obtain ⟨hp, hq⟩ := reindex_sums b hb σ hσ x
  simp only [weight, hp, hq]
#print axioms Paper7PruningCanonical.reindex_weight

theorem reindex_theta (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) : theta (reindex σ x) = theta x :=
  (dihedral_bijective b hb σ hσ).sum_comp (fun i => thetaV (x.1 i) (x.2 i))
#print axioms Paper7PruningCanonical.reindex_theta

theorem reindex_budget_iff (b N : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) : Budget b N (reindex σ x) ↔ Budget b N x := by
  simp only [Budget, reindex_weight b hb σ hσ x]
#print axioms Paper7PruningCanonical.reindex_budget_iff

theorem reindex_sg_iso (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) :
    Nonempty (SG b x.1 x.2 ≃g SG b (reindex σ x).1 (reindex σ x).2) :=
  Paper7Setup.sg_iso_of_dihedral b x.1 x.2 _ _ hb σ hσ rfl rfl
#print axioms Paper7PruningCanonical.reindex_sg_iso

/-- Transfer the actual complex spectrum through the full graph isomorphism. -/
theorem integral_graphIso_iff {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) :
    IsIntegralGraph H ↔ IsIntegralGraph G := by
  have hpoly : (H.adjMatrix ℂ).charpoly = (G.adjMatrix ℂ).charpoly := by
    rw [← e.reindex_adjMatrix ℂ]
    exact Matrix.charpoly_reindex e.toEquiv (G.adjMatrix ℂ)
  have hspec : spectrum ℂ (H.adjMatrix ℂ) = spectrum ℂ (G.adjMatrix ℂ) := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.mem_spectrum_iff_isRoot_charpoly, hpoly]
  unfold IsIntegralGraph
  rw [hspec]
#print axioms Paper7PruningCanonical.integral_graphIso_iff

theorem reindex_integral_iff (b : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) :
    IsIntegralGraph (SG b (reindex σ x).1 (reindex σ x).2) ↔
      IsIntegralGraph (SG b x.1 x.2) := by
  obtain ⟨e⟩ := reindex_sg_iso b hb σ hσ x
  exact integral_graphIso_iff _ _ e
#print axioms Paper7PruningCanonical.reindex_integral_iff

/-- The base 64 key argument really uses the original budget. -/
theorem budget_coordinate_lt_64 (b N : ℕ) (x : PQ b) (hN : N ≤ 49)
    (hx : Budget b N x) (i : Fin b) : x.1 i < 64 := by
  have hi : x.1 i ≤ pSum x :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (x.1 j)) (Finset.mem_univ i)
  have hw := hx.2
  unfold weight at hw
  omega
#print axioms Paper7PruningCanonical.budget_coordinate_lt_64

/-- In keyWeight, the final p digit cannot outweigh a one-unit change in load.
It is insufficient to infer this from key maximality without the budget. -/
theorem weight_rotation_of_canonical (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49)
    (x : PQ b) (hx : Budget b N x) (hcan : Canonical keyWeight true b x) :
    RotationRule (fun p q => p + 2*q) b x := by
  have hrot := greatest_canonical_rotation b (by omega) keyWeight x hcan
  intro i j hj
  have hij := hrot i j hj
  have hpj := budget_coordinate_lt_64 b N x hN hx j
  unfold keyWeight at hij
  dsimp only at ⊢
  omega
#print axioms Paper7PruningCanonical.weight_rotation_of_canonical

end Paper7PruningCanonical
