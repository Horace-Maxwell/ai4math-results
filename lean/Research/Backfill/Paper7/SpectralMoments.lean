import Research.Backfill.Paper7.ChallengeV3

/-! Generic spectral moments, with the exact multiset multiplicities used by
the frozen graph contract. This module proves no complete paper contract. -/

set_option autoImplicit false

noncomputable section

open Polynomial Finset
open BackfillPaper7.Challenge

namespace Paper7Moments

theorem trace_unitary_conjugation {V : Type} [Fintype V] [DecidableEq V]
    (U : Matrix.unitaryGroup V ℝ) (A : Matrix V V ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem realHermitian_moment {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (A.charpoly.roots.map (fun x => x ^ k)).sum = (A ^ k).trace := by
  have htrace : (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
    calc
      (A ^ k).trace =
          ((Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))) ^ k).trace :=
        congrArg (fun B : Matrix V V ℝ => (B ^ k).trace) hA.spectral_theorem
      _ = ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) ^ k).trace := by
        rw [← map_pow, trace_unitary_conjugation]
      _ = ∑ i, (hA.eigenvalues i) ^ k := by
        simp only [Matrix.diagonal_pow, Matrix.trace_diagonal,
          Pi.pow_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simpa only [Finset.sum, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq] using htrace.symm

theorem adjMatrix_map {V R S : Type} [CommRing R] [CommRing S]
    (H : SimpleGraph V) [DecidableRel H.Adj] (c : R →+* S) :
    (H.adjMatrix R).map c = H.adjMatrix S := by
  ext i j
  by_cases hij : H.Adj i j
  · simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply, hij, ite_true, map_one]
  · simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply, hij, ite_false, map_zero]

theorem graph_moment_eq_int_trace {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) :
    ((spec H).map (fun x => x ^ k)).sum = (((H.adjMatrix ℤ) ^ k).trace : ℝ) := by
  have hH : (H.adjMatrix ℝ).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr H.isSymm_adjMatrix
  change ((H.adjMatrix ℝ).charpoly.roots.map (fun x => x ^ k)).sum = _
  rw [realHermitian_moment _ hH k]
  let c : Matrix V V ℤ →+* Matrix V V ℝ := (Int.castRingHom ℝ).mapMatrix
  have hc : c (H.adjMatrix ℤ) = H.adjMatrix ℝ := adjMatrix_map H (Int.castRingHom ℝ)
  have hcpow : c ((H.adjMatrix ℤ) ^ k) = (H.adjMatrix ℝ) ^ k := by
    rw [map_pow, hc]
  calc
    ((H.adjMatrix ℝ) ^ k).trace = (c ((H.adjMatrix ℤ) ^ k)).trace :=
      congrArg Matrix.trace hcpow.symm
    _ = (((H.adjMatrix ℤ) ^ k).trace : ℝ) :=
      (AddMonoidHom.map_trace (Int.castRingHom ℝ) ((H.adjMatrix ℤ) ^ k)).symm

theorem graph_first_moment_zero {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : (spec H).sum = 0 := by
  simpa only [pow_one, Multiset.map_id', SimpleGraph.trace_adjMatrix,
    Int.cast_zero] using graph_moment_eq_int_trace H 1

/-- The complex-spectrum integrality predicate implies integrality of each
entry of the real characteristic-root multiset. -/
theorem integral_spec_entry {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : IsIntegralGraph H)
    (x : ℝ) (hx : x ∈ spec H) : ∃ z : ℤ, x = (z : ℝ) := by
  have hroot : Polynomial.IsRoot (H.adjMatrix ℝ).charpoly x :=
    Polynomial.isRoot_of_mem_roots hx
  have hrootC : Polynomial.IsRoot (H.adjMatrix ℂ).charpoly (x : ℂ) := by
    rw [← adjMatrix_map H (algebraMap ℝ ℂ), Matrix.charpoly_map]
    change (((H.adjMatrix ℝ).charpoly).map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) x) = 0
    rw [Polynomial.eval_map_apply, hroot.eq_zero, map_zero]
  obtain ⟨z, hz⟩ := hH (x : ℂ) (Matrix.mem_spectrum_of_isRoot_charpoly hrootC)
  refine ⟨z, ?_⟩
  have hre := congrArg Complex.re hz
  simpa using hre

end Paper7Moments

#print axioms Paper7Moments.trace_unitary_conjugation
#print axioms Paper7Moments.realHermitian_moment
#print axioms Paper7Moments.adjMatrix_map
#print axioms Paper7Moments.graph_moment_eq_int_trace
#print axioms Paper7Moments.graph_first_moment_zero
#print axioms Paper7Moments.integral_spec_entry
