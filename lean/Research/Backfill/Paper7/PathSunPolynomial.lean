import Research.Backfill.Paper7.PathSunEdgeBlocks

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Classical

theorem vertexPairs_eq_ofFn (b : ℕ) (p q : Fin b → ℕ) :
    vertexPairs b p q = List.ofFn (fun i => (p i,q i)) := by
  exact List.ofFn_eq_map.symm
#print axioms Paper7Schwenk.vertexPairs_eq_ofFn

theorem sunDeleteEdge_eval_chain {K : Type*} [Field K] (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (u v : Fin b) (hu : u.val=0) (hv : v.val+1=b)
    (x : K) (hx : x≠0) (hquad : x^2-1≠0) :
    Polynomial.eval₂RingHom (Int.castRingHom K) x
      (graphPhi (sunDeleteEdge b (pq b p q) u v)) =
    Polynomial.eval₂RingHom (Int.castRingHom K) x
      (chainPolynomial (vertexPairs b p q)) := by
  let : Invertible (pendantShift b (pq b p q) x) :=
    Matrix.invertibleOfIsUnitDet _ (pendantShift_isUnit_det b p q x hx hquad)
  have hevX : Polynomial.eval₂RingHom (Int.castRingHom K) x X = x :=
    Polynomial.eval₂_X _ _
  have hchain := chain_eval_schur (Polynomial.eval₂RingHom (Int.castRingHom K) x)
    (by simpa only [hevX] using hx)
    (by simpa only [hevX] using hquad) b p q
  simp only [map_legPolynomial, hevX, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hchain
  have hphi : Polynomial.eval₂RingHom (Int.castRingHom K) x
      (graphPhi (sunDeleteEdge b (pq b p q) u v)) =
      (x ^ totalP b p * (x^2-1)^totalQ b q) *
        (weightedPath (fun i => x-(p i : K)/x-(q i : K)*x/(x^2-1)) (fun _ => 1)).det := by
    rw [graphPhi_eval_det_shift, sunDeleteEdge_shift_blocks b (pq b p q) hb u v hu hv x,
      Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
      attachment_inverse_coupling b p q x hx hquad, pathShift_schur, pendantShift_det]
  rw [vertexPairs_eq_ofFn, hchain]
  simpa only [totalP, totalQ] using hphi
#print axioms Paper7Schwenk.sunDeleteEdge_eval_chain

abbrev SchwenkField := FractionRing (Polynomial ℤ)
#print axioms Paper7Schwenk.SchwenkField

def schwenkMap : Polynomial ℤ →+* SchwenkField := algebraMap _ _
#print axioms Paper7Schwenk.schwenkMap

theorem schwenkMap_injective : Function.Injective schwenkMap :=
  IsFractionRing.injective (Polynomial ℤ) SchwenkField
#print axioms Paper7Schwenk.schwenkMap_injective

theorem schwenkMap_X_ne_zero : schwenkMap X ≠ 0 := by
  intro h
  exact Polynomial.X_ne_zero (schwenkMap_injective (by simpa only [map_zero] using h))
#print axioms Paper7Schwenk.schwenkMap_X_ne_zero

theorem schwenkMap_quad_ne_zero : (schwenkMap X)^2-1 ≠ 0 := by
  intro h
  have hB : (X^2-1 : Polynomial ℤ)=0 :=
    schwenkMap_injective (by simpa only [map_sub, map_pow, map_one, map_zero] using h)
  exact (monic_X_pow_sub_one (R:=ℤ) (n:=2) (by decide)).ne_zero hB
#print axioms Paper7Schwenk.schwenkMap_quad_ne_zero

theorem schwenkMap_eq_eval :
    Polynomial.eval₂RingHom (Int.castRingHom SchwenkField) (schwenkMap X) = schwenkMap := by
  apply Polynomial.ringHom_ext
  · intro z
    change (Polynomial.C z).eval₂ (Int.castRingHom SchwenkField) (schwenkMap X) =
      schwenkMap (Polynomial.C z)
    rw [Polynomial.eval₂_C]
    have hC : Polynomial.C z = (z : Polynomial ℤ) := map_intCast Polynomial.C z
    rw [hC, map_intCast]
    rfl
  · exact Polynomial.eval₂_X _ _
#print axioms Paper7Schwenk.schwenkMap_eq_eval

/-- Full first equality of the frozen recurrence, with the original graph. -/
theorem sunDeleteEdge_chainPolynomial (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (u v : Fin b) (hu : u.val=0) (hv : v.val+1=b) :
    graphPhi (sunDeleteEdge b (pq b p q) u v) = chainPolynomial (vertexPairs b p q) := by
  apply schwenkMap_injective
  have h := sunDeleteEdge_eval_chain b p q hb u v hu hv (schwenkMap X)
    schwenkMap_X_ne_zero schwenkMap_quad_ne_zero
  rwa [schwenkMap_eq_eval] at h
#print axioms Paper7Schwenk.sunDeleteEdge_chainPolynomial

end Paper7Schwenk
