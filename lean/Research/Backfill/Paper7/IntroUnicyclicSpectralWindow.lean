import Research.Backfill.Paper7.IntroUnicyclicDegreeMass
import Research.Backfill.Paper7.SpectralMoments

/-! Source-only spectral window for arbitrary finite unicyclic graphs.
The final theorem has precisely the graph hypotheses, not a supplied
root profile or an assumed generalized-sun representation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace Paper7IntroGeneral
open SimpleGraph BackfillPaper7.Challenge

theorem eigenvector_square_le_neighbor_degree_bound
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℝ)
    (hB : ∀ v, (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) ≤ B)
    (lam : ℝ) (x : V → ℝ) (hx : x ≠ 0)
    (he : G.adjMatrix ℝ *ᵥ x = lam • x) : lam ^ 2 ≤ B := by
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun v => |x v|) Finset.univ_nonempty
  have hmax' (v : V) : |x v| ≤ |x i| := hmax v (Finset.mem_univ v)
  have hxi : x i ≠ 0 := by
    intro hz
    apply hx
    funext v
    have hv := hmax' v
    rw [hz, abs_zero] at hv
    exact abs_eq_zero.mp (le_antisymm hv (abs_nonneg _))
  have hpos : 0 < |x i| := abs_pos.mpr hxi
  have hrow (v : V) : (∑ u ∈ G.neighborFinset v, x u) = lam * x v := by
    have hv := congrFun he v
    simpa only [G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using hv
  have htwo : lam ^ 2 * x i =
      ∑ u ∈ G.neighborFinset i, ∑ w ∈ G.neighborFinset u, x w := by
    calc
      _ = lam * (lam * x i) := by ring
      _ = lam * (∑ u ∈ G.neighborFinset i, x u) := by rw [hrow]
      _ = ∑ u ∈ G.neighborFinset i, lam * x u := Finset.mul_sum ..
      _ = _ := Finset.sum_congr rfl (fun u _hu => (hrow u).symm)
  have hinner (u : V) : |∑ w ∈ G.neighborFinset u, x w| ≤
      (G.degree u : ℝ) * |x i| := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset u, |x w| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _w ∈ G.neighborFinset u, |x i| :=
        Finset.sum_le_sum (fun w _hw => hmax' w)
      _ = _ := by simp
  have hbound : lam ^ 2 * |x i| ≤ B * |x i| := by
    calc
      _ = |lam ^ 2 * x i| := by rw [abs_mul, abs_of_nonneg (sq_nonneg lam)]
      _ = |∑ u ∈ G.neighborFinset i, ∑ w ∈ G.neighborFinset u, x w| :=
        congrArg abs htwo
      _ ≤ ∑ u ∈ G.neighborFinset i, |∑ w ∈ G.neighborFinset u, x w| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ u ∈ G.neighborFinset i, (G.degree u : ℝ) * |x i| :=
        Finset.sum_le_sum (fun u _hu => hinner u)
      _ = (∑ u ∈ G.neighborFinset i, (G.degree u : ℝ)) * |x i| :=
        (Finset.sum_mul ..).symm
      _ ≤ B * |x i| := mul_le_mul_of_nonneg_right (hB i) (abs_nonneg _)
  exact (mul_le_mul_iff_left₀ hpos).mp hbound
#print axioms Paper7IntroGeneral.eigenvector_square_le_neighbor_degree_bound

theorem unicyclic_real_root_square_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) (lam : ℝ)
    (hlam : lam ∈ spec G) : lam ^ 2 ≤ (Fintype.card V : ℝ) + 1 := by
  let : Nonempty V := hG.1.nonempty
  have hroot : (G.adjMatrix ℝ).charpoly.IsRoot lam :=
    Polynomial.isRoot_of_mem_roots hlam
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) lam := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    simpa only [Matrix.charpoly_toLin'] using hroot
  obtain ⟨x, hxe, hx⟩ := hev.exists_hasEigenvector
  refine eigenvector_square_le_neighbor_degree_bound G
    ((Fintype.card V : ℝ) + 1) ?_ lam x hx ?_
  · intro v
    exact_mod_cast unicyclic_neighbor_degree_sum_le G hG v
  · simpa only [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hxe
#print axioms Paper7IntroGeneral.unicyclic_real_root_square_le

theorem integral_unicyclic21_spectrum_window
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {b : ℕ}
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (lam : ℝ) (hlam : lam ∈ spec G) :
    ∃ z : ℤ, lam = (z : ℝ) ∧ -4 ≤ z ∧ z ≤ 4 := by
  obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry G hI lam hlam
  have hs := unicyclic_real_root_square_le G hG lam hlam
  have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
  have hzsq : (z : ℝ) ^ 2 ≤ 22 := by rw [hz] at hs; linarith
  have hlo : -4 ≤ z := by
    by_contra h
    have hz5 : z ≤ -5 := by omega
    have hz5R : (z : ℝ) ≤ -5 := by exact_mod_cast hz5
    nlinarith [sq_nonneg ((z : ℝ) + 5)]
  have hhi : z ≤ 4 := by
    by_contra h
    have hz5 : 5 ≤ z := by omega
    have hz5R : (5 : ℝ) ≤ z := by exact_mod_cast hz5
    nlinarith [sq_nonneg ((z : ℝ) - 5)]
  exact ⟨z, hz, hlo, hhi⟩
#print axioms Paper7IntroGeneral.integral_unicyclic21_spectrum_window

end Paper7IntroGeneral
