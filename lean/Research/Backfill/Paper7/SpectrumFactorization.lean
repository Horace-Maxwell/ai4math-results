import Research.Backfill.Paper7.SpectrumGraphBasics

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Spectrum

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem integral_iff_integerFactorization {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsIntegralGraph G ↔ ∃ S : Finset ℤ, IntegerFactorizationOn (graphPhi G) S := by
  classical
  constructor
  · intro hG
    have hs : (graphPhi G).Splits := by
      apply Polynomial.Splits.of_splits_map_of_injective
        (i := Int.castRingHom ℂ) Int.cast_injective
        (IsAlgClosed.splits ((graphPhi G).map (Int.castRingHom ℂ)))
      intro μ hμ
      have hroot : Polynomial.IsRoot (G.adjMatrix ℂ).charpoly μ := by
        rw [← graphPhi_map G ℂ]
        exact Polynomial.isRoot_of_mem_roots hμ
      obtain ⟨z, hz⟩ := hG μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot)
      exact ⟨z, hz.symm⟩
    have hm : (graphPhi G).Monic := by
      unfold graphPhi
      exact Matrix.charpoly_monic _
    refine ⟨(graphPhi G).roots.toFinset, (graphPhi G).roots.toList, ?_, ?_⟩
    · intro z hz
      exact Multiset.mem_toFinset.mpr (Multiset.mem_toList.mp hz)
    · have hprod : ((graphPhi G).roots.toList.map (fun z : ℤ => X - C z)).prod =
          ((graphPhi G).roots.map (fun z : ℤ => X - C z)).prod := by
        have h := congrArg Multiset.prod
          (congrArg (Multiset.map (fun z : ℤ => (X - C z : Polynomial ℤ)))
            (Multiset.coe_toList (graphPhi G).roots))
        simpa only [Multiset.map_coe, Multiset.prod_coe] using h
      exact (hs.eq_prod_roots_of_monic hm).trans hprod.symm
  · rintro ⟨_S, a, _haS, ha⟩
    have hs : (graphPhi G).Splits := by
      rw [ha]
      apply Polynomial.Splits.listProd
      intro f hf
      obtain ⟨z, _hz, rfl⟩ := List.mem_map.mp hf
      exact Polynomial.Splits.X_sub_C z
    intro μ hμ
    have hroot : μ ∈ (G.adjMatrix ℂ).charpoly.roots :=
      (Polynomial.mem_roots (G.adjMatrix ℂ).charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ)
    rw [← graphPhi_map G ℂ,
      hs.roots_map_of_injective (i := Int.castRingHom ℂ) Int.cast_injective] at hroot
    obtain ⟨z, _hz, hz⟩ := Multiset.mem_map.mp hroot
    exact ⟨z, hz.symm⟩

#print axioms Paper7Spectrum.integral_iff_integerFactorization

end Paper7Spectrum
