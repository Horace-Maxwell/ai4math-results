import Research.Backfill.Paper7.SpectrumFactorization
import Research.Backfill.Paper7.ClearedCharacteristicPolynomial

/-! Source-only candidate: not compiled, zero new formal credit.
The cleared identity is used with all its original nonnegative exponents.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7SpectralWindow

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem integerFactorizationOn_splits_roots {f : Polynomial ℤ} {S : Finset ℤ}
    (hf : IntegerFactorizationOn f S) :
    f.Splits ∧ ∀ z ∈ f.roots, z ∈ S := by
  classical
  obtain ⟨a, ha, rfl⟩ := hf
  constructor
  · apply Polynomial.Splits.listProd
    intro g hg
    obtain ⟨z, _hz, rfl⟩ := List.mem_map.mp hg
    exact Polynomial.Splits.X_sub_C z
  · have hroots : ((a.map (fun z : ℤ => X - C z)).prod).roots = (a : Multiset ℤ) := by
      simpa only [Multiset.map_coe, Multiset.prod_coe] using
        Polynomial.roots_multiset_prod_X_sub_C (a : Multiset ℤ)
    intro z hz
    rw [hroots] at hz
    exact ha z (by simpa only [Multiset.mem_coe] using hz)

#print axioms Paper7SpectralWindow.integerFactorizationOn_splits_roots

theorem integerFactorizationOn_of_splits {f : Polynomial ℤ} {S : Finset ℤ}
    (hm : f.Monic) (hs : f.Splits) (hroots : ∀ z ∈ f.roots, z ∈ S) :
    IntegerFactorizationOn f S := by
  classical
  refine ⟨f.roots.toList, ?_, ?_⟩
  · intro z hz
    exact hroots z (Multiset.mem_toList.mp hz)
  · have hprod : (f.roots.toList.map (fun z : ℤ => X - C z)).prod =
        (f.roots.map (fun z : ℤ => X - C z)).prod := by
      have h := congrArg Multiset.prod
        (congrArg (Multiset.map (fun z : ℤ => (X - C z : Polynomial ℤ)))
          (Multiset.coe_toList f.roots))
      simpa only [Multiset.map_coe, Multiset.prod_coe] using h
    exact (hs.eq_prod_roots_of_monic hm).trans hprod.symm

#print axioms Paper7SpectralWindow.integerFactorizationOn_of_splits

theorem integerFactorizationOn_of_monic_dvd {f g : Polynomial ℤ} {S : Finset ℤ}
    (hf : f.Monic) (hg : g ≠ 0) (hfg : f ∣ g)
    (hfactor : IntegerFactorizationOn g S) : IntegerFactorizationOn f S := by
  have hdata := integerFactorizationOn_splits_roots hfactor
  apply integerFactorizationOn_of_splits hf (hdata.1.of_dvd hg hfg)
  intro z hz
  exact hdata.2 z (Multiset.mem_of_le (Polynomial.roots.le_of_dvd hg hfg) hz)

#print axioms Paper7SpectralWindow.integerFactorizationOn_of_monic_dvd

theorem integerFactorizationOn_mul {f g : Polynomial ℤ} {S : Finset ℤ}
    (hf : IntegerFactorizationOn f S) (hg : IntegerFactorizationOn g S) :
    IntegerFactorizationOn (f * g) S := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨c, hc, hgc⟩ := hg
  refine ⟨a ++ c, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ha z hz
    · exact hc z hz
  · simp only [List.map_append, List.prod_append, ← hfa, ← hgc]

#print axioms Paper7SpectralWindow.integerFactorizationOn_mul

theorem denominator_integerFactorization (u v : ℕ) :
    IntegerFactorizationOn (X ^ u * (X ^ 2 - 1) ^ v) (integerWindow 9) := by
  refine ⟨(List.replicate u 0 ++ List.replicate v 1) ++ List.replicate v (-1), ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · have hz0 : z = 0 := List.eq_of_mem_replicate hz
        subst z
        norm_num [integerWindow]
      · have hz1 : z = 1 := List.eq_of_mem_replicate hz
        subst z
        norm_num [integerWindow]
    · have hzn1 : z = -1 := List.eq_of_mem_replicate hz
      subst z
      norm_num [integerWindow]
  · simp only [List.map_append, List.prod_append, List.map_replicate,
      List.prod_replicate, map_zero, map_one, map_neg, sub_zero, sub_neg_eq_add]
    have hquad : (X ^ 2 - 1 : Polynomial ℤ) = (X - 1) * (X + 1) := by ring
    rw [hquad, mul_pow, mul_assoc]

#print axioms Paper7SpectralWindow.denominator_integerFactorization

theorem graph_integerFactorization_window {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hwin : ∀ x ∈ spec G, |x| < 10) (hG : IsIntegralGraph G) :
    IntegerFactorizationOn (graphPhi G) (integerWindow 9) := by
  classical
  obtain ⟨_S, hfactor⟩ := (Paper7Spectrum.integral_iff_integerFactorization G).mp hG
  have hs : (graphPhi G).Splits := (integerFactorizationOn_splits_roots hfactor).1
  have hm : (graphPhi G).Monic := Matrix.charpoly_monic _
  apply integerFactorizationOn_of_splits hm hs
  intro z hz
  have hroot : Polynomial.IsRoot ((graphPhi G).map (Int.castRingHom ℝ)) (z : ℝ) :=
    (Polynomial.isRoot_of_mem_roots hz).map
  rw [Paper7Spectrum.graphPhi_map G ℝ] at hroot
  have hspec : (z : ℝ) ∈ spec G :=
    (Polynomial.mem_roots (G.adjMatrix ℝ).charpoly_monic.ne_zero).mpr hroot
  have habs := hwin (z : ℝ) hspec
  have hlo : (-10 : ℤ) < z := by exact_mod_cast (abs_lt.mp habs).1
  have hhi : z < (10 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  change z ∈ Finset.Icc (-(9 : ℤ)) (9 : ℤ)
  rw [Finset.mem_Icc]
  omega

#print axioms Paper7SpectralWindow.graph_integerFactorization_window

theorem sun_integer_factorization (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hwin : ∀ x ∈ spec (SG b p q), |x| < 10) (hG : IsIntegralGraph (SG b p q)) :
    IntegerFactorizationOn (graphPhi (SG b p q)) (integerWindow 9) ∧
      IntegerFactorizationOn (clearedF b p q) (integerWindow 9) := by
  classical
  have hphi := graph_integerFactorization_window (SG b p q) hwin hG
  have hidentity := Paper7Cleared.cleared_identity b p q hb
  have hF : (clearedF b p q).Monic :=
    (Paper7Cleared.monic_degree_of_cleared_identity b p q hidentity).1
  have hPhi : (graphPhi (SG b p q)).Monic := Matrix.charpoly_monic _
  have hright : (X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q) : Polynomial ℤ) ≠ 0 :=
    ((Paper7Cleared.monic_denominator_factor b b).mul hPhi).ne_zero
  have hdvd : clearedF b p q ∣ X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q) := by
    refine ⟨X ^ totalP b p * (X ^ 2 - 1) ^ totalQ b q, ?_⟩
    exact hidentity.symm.trans (mul_comm _ _)
  exact ⟨hphi, integerFactorizationOn_of_monic_dvd hF hright hdvd
    (integerFactorizationOn_mul (denominator_integerFactorization b b) hphi)⟩

#print axioms Paper7SpectralWindow.sun_integer_factorization

end Paper7SpectralWindow
