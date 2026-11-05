import Research.Backfill.Paper7.IntroCycleRepeatedRoots
import Research.Backfill.Paper7.IntroSeparatedPartitionSpectrum
import Research.Backfill.Paper7.IntroDeletedVertexGap

/-! Integrality passes to a genuine isolated cycle side of a vertex deletion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroBareSide
open SimpleGraph Matrix Polynomial BackfillPaper7.Challenge Paper7Lemma41 Paper7IntroCutGap

theorem separated_isomorphic_cycle_count_le
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Set W)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬H.Adj i j) (b : ℕ)
    (e : H.induce S ≃g cycleGraph b) (x : ℝ) :
    (spec (cycleGraph b)).count x ≤ (spec H).count x := by
  have hpoly : ((cycleGraph b).adjMatrix ℝ).charpoly =
      ((H.induce S).adjMatrix ℝ).charpoly := by
    rw [← e.reindex_adjMatrix ℝ]
    exact Matrix.charpoly_reindex e.toEquiv ((H.induce S).adjMatrix ℝ)
  have hspec : spec (cycleGraph b) = spec (H.induce S) :=
    congrArg Polynomial.roots hpoly
  rw [hspec, separated_partition_spec H S hsep, Multiset.count_add]
  omega
#print axioms Paper7IntroBareSide.separated_isomorphic_cycle_count_le

theorem integral_deleted_isolated_cycle_real_roots_integer
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (S : Set {w : V // w ≠ v})
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬(vertexDeletedGraph G v).Adj i j)
    (b : ℕ) (hb : 3 ≤ b) (e : (vertexDeletedGraph G v).induce S ≃g cycleGraph b) :
    ∀ x ∈ spec (cycleGraph b), ∃ z : ℤ, x = (z : ℝ) := by
  let : NeZero b := ⟨by omega⟩
  intro x hx
  by_contra hn
  have htwo := cycle_noninteger_root_count_ge_two b hb x hx hn
  have hcount := separated_isomorphic_cycle_count_le (vertexDeletedGraph G v) S hsep b e x
  exact hn (integral_vertex_deleted_repeated_root_integer G hI v x (htwo.trans hcount))
#print axioms Paper7IntroBareSide.integral_deleted_isolated_cycle_real_roots_integer

theorem integral_deleted_isolated_cycle_integral
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (S : Set {w : V // w ≠ v})
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬(vertexDeletedGraph G v).Adj i j)
    (b : ℕ) (hb : 3 ≤ b) (e : (vertexDeletedGraph G v).induce S ≃g cycleGraph b) :
    IsIntegralGraph (cycleGraph b) := by
  let : NeZero b := ⟨by omega⟩
  have hreal := integral_deleted_isolated_cycle_real_roots_integer G hI v S hsep b hb e
  intro μ hμ
  have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
  have hprod : (∏ k : ZMod b,
      (μ - (ZMod.stdAddChar k + ZMod.stdAddChar (-k)))) = 0 := by
    simpa only [Polynomial.IsRoot, cycleGraph_charpoly_complex b hb,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hroot
  obtain ⟨k, _hk, hk⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hμk : μ = (cycleCosine b k : ℂ) := by
    rw [← character_pair_eq_cycleCosine b k]
    exact sub_eq_zero.mp hk
  have hkreal : cycleCosine b k ∈ spec (cycleGraph b) := by
    rw [cycleGraph_spec b hb]
    exact Multiset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
  obtain ⟨z, hz⟩ := hreal (cycleCosine b k) hkreal
  refine ⟨z, hμk.trans ?_⟩
  exact_mod_cast hz
#print axioms Paper7IntroBareSide.integral_deleted_isolated_cycle_integral

end Paper7IntroBareSide
