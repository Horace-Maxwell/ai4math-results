import Research.Backfill.Paper7.EndpointSunCoordinates

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Classical

theorem interior_attachment_coupling {K : Type*} [Field K] (n : ℕ)
    (p q : Fin (n+2) → ℕ) (x : K) (hx : x≠0) (hquad : x^2-1≠0) :
    let B := (attachment (K:=K) (n+2) (pq (n+2) p q)).submatrix (interiorIndex n) id
    B * (pendantShift (n+2) (pq (n+2) p q) x)⁻¹ * B.transpose =
      Matrix.diagonal (fun i => (p (interiorIndex n i) : K)/x +
        (q (interiorIndex n i) : K)*x/(x^2-1)) := by
  let A := attachment (K:=K) (n+2) (pq (n+2) p q)
  let D := pendantShift (n+2) (pq (n+2) p q) x
  change A.submatrix (interiorIndex n) id * D⁻¹ *
    (A.submatrix (interiorIndex n) id).transpose = _
  have ht : (A.submatrix (interiorIndex n) id).transpose =
      A.transpose.submatrix id (interiorIndex n) := rfl
  have hmul := Matrix.submatrix_mul A D⁻¹ (interiorIndex n) id id Function.bijective_id
  simp only [Matrix.submatrix_id_id] at hmul
  rw [ht, ← hmul, ← Matrix.submatrix_mul (A*D⁻¹) A.transpose
    (interiorIndex n) id (interiorIndex n) Function.bijective_id]
  exact (congrArg (fun M : Matrix (Fin (n+2)) (Fin (n+2)) K =>
    M.submatrix (interiorIndex n) (interiorIndex n))
      (attachment_inverse_coupling (n+2) p q x hx hquad)).trans
        (Matrix.submatrix_diagonal _ _ (interiorIndex_injective n))
#print axioms Paper7Schwenk.interior_attachment_coupling

theorem prod_endpoints_interior {K : Type*} [CommMonoid K] (n : ℕ)
    (f : Fin (n+2) → K) :
    (∏ i, f i) = f 0 * f (Fin.last (n+1)) * ∏ i : Fin n, f (interiorIndex n i) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  have hlast : (Fin.last n).succ = Fin.last (n+1) := rfl
  rw [hlast]
  change f 0 * ((∏ i : Fin n, f (interiorIndex n i)) * f (Fin.last (n+1))) = _
  ac_rfl
#print axioms Paper7Schwenk.prod_endpoints_interior

theorem vertexPairs_trim_endpoints (n : ℕ) (p q : Fin (n+2) → ℕ) :
    ((vertexPairs (n+2) p q).drop 1).dropLast =
      List.ofFn (fun i : Fin n => (p (interiorIndex n i),q (interiorIndex n i))) := by
  rw [vertexPairs_eq_ofFn, List.ofFn_succ]
  simp only [List.drop_succ_cons, List.drop_zero]
  have hidx (i : Fin n) : i.castSucc.succ = interiorIndex n i := by
    apply Fin.ext
    rfl
  simpa only [List.concat_eq_append, List.dropLast_concat, hidx] using congrArg List.dropLast
    (List.ofFn_succ' (fun i : Fin (n+1) => (p i.succ,q i.succ)))
#print axioms Paper7Schwenk.vertexPairs_trim_endpoints

theorem endpointDelete_eval_chain {K : Type*} [Field K] (n : ℕ)
    (p q : Fin (n+2) → ℕ) (hn : 1 ≤ n) (x : K) (hx : x≠0) (hquad : x^2-1≠0) :
    Polynomial.eval₂RingHom (Int.castRingHom K) x
      (graphPhi (deleteVertices (SG (n+2) p q)
        ({Sum.inl 0,Sum.inl (Fin.last (n+1))} : Set (SunV (n+2) (pq (n+2) p q))))) =
    Polynomial.eval₂RingHom (Int.castRingHom K) x
      (legPolynomial (p 0) (q 0) * legPolynomial (p (Fin.last (n+1))) (q (Fin.last (n+1))) *
        chainPolynomial (((vertexPairs (n+2) p q).drop 1).dropLast)) := by
  have hevX : Polynomial.eval₂RingHom (Int.castRingHom K) x X = x :=
    Polynomial.eval₂_X _ _
  let : Invertible (pendantShift (n+2) (pq (n+2) p q) x) :=
    Matrix.invertibleOfIsUnitDet _ (pendantShift_isUnit_det (n+2) p q x hx hquad)
  rw [vertexPairs_trim_endpoints, map_mul, map_mul]
  rw [chain_eval_schur (Polynomial.eval₂RingHom (Int.castRingHom K) x)
    (by simpa only [hevX] using hx)
    (by simpa only [hevX] using hquad)]
  simp only [map_legPolynomial, hevX]
  rw [graphPhi_eval_det_shift]
  rw [← Matrix.det_reindex_self (endpointComplementEquiv (n:=n) (pq (n+2) p q))]
  rw [endpointDelete_shift_blocks n (pq (n+2) p q) hn x,
    Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    interior_attachment_coupling n p q x hx hquad]
  have hschur := pathShift_schur n (p ∘ interiorIndex n) (q ∘ interiorIndex n) x
  dsimp only [Function.comp_apply] at hschur
  rw [hschur, pendantShift_det]
  have hprod : x ^ totalP (n+2) p * (x^2-1)^totalQ (n+2) q =
      ∏ i : Fin (n+2), x^(p i)*(x^2-1)^(q i) := by
    simp only [totalP, totalQ, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod, prod_endpoints_interior]
  ring
#print axioms Paper7Schwenk.endpointDelete_eval_chain

/-- Full second equality of the frozen recurrence, including its exact
middle list and both endpoint factors of detached arms. -/
theorem endpointDelete_chainPolynomial (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (u v : Fin b) (hu : u.val=0) (hv : v.val+1=b) :
    graphPhi (deleteVertices (SG b p q)
      ({Sum.inl u,Sum.inl v} : Set (SunV b (pq b p q)))) =
      legPolynomial (p u) (q u) * legPolynomial (p v) (q v) *
        chainPolynomial (((vertexPairs b p q).drop 1).dropLast) := by
  obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2, by omega⟩
  have hu' : u=0 := Fin.ext hu
  have hv' : v=Fin.last (n+1) := by apply Fin.ext; change v.val=n+1; omega
  subst u
  subst v
  apply schwenkMap_injective
  have h := endpointDelete_eval_chain n p q (by omega) (schwenkMap X)
    schwenkMap_X_ne_zero schwenkMap_quad_ne_zero
  rwa [schwenkMap_eq_eval] at h
#print axioms Paper7Schwenk.endpointDelete_chainPolynomial

end Paper7Schwenk
