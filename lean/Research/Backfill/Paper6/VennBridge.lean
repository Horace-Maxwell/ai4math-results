import Research.Backfill.Paper6.P2
import Research.Backfill.Paper6.InclusionExclusionVenn
import Research.Backfill.Paper6.AffineInvariance

/-!
# Exact polynomial-to-Venn semantics for the frozen Proposition E work

This module is a complete generic bridge, not a proof of PropE, PropE_counts,
or PropE_remark_2mod4. The remaining finite certificate is not assumed here.
Every original polynomial term is retained after replacing positive exponents
by variable membership, so constants, repeated supports and cancellation are
all included. The resulting data satisfy the actual frozen vennVectors bounds.
-/

set_option autoImplicit false

namespace Paper6FiveMonomials

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

abbrev Region (k : ℕ) := {T : Finset (Fin k) // T.Nonempty}

/-- Actual sizes of nonempty membership-pattern regions, bounded by the fourteen coordinates. -/
def regionCount {k : ℕ} (S : Fin k → Finset (Fin 14)) : Region k → Fin 15 :=
  fun T => ⟨(venn S T.1).card, by
    have h : (venn S T.1).card ≤ 14 := by
      simpa only [Fintype.card_fin] using (venn S T.1).card_le_univ
    omega⟩

def memberRegions {k : ℕ} (i : Fin k) : Finset (Region k) :=
  Finset.univ.filter fun T => i ∈ T.1

def meetingRegions {k : ℕ} (T : Finset (Fin k)) : Finset (Region k) :=
  Finset.univ.filter fun U => (T ∩ U.1).Nonempty

theorem distinct_regions_disjoint {k : ℕ} (S : Fin k → Finset (Fin 14))
    (U V : Region k) (hne : U ≠ V) : Disjoint (venn S U.1) (venn S V.1) := by
  apply venn_disjoint S
  intro heq
  exact hne (Subtype.ext heq)

/-- Every partial collection of regions is a disjoint union, not just an abstract size vector. -/
theorem region_union_card {k : ℕ} (S : Fin k → Finset (Fin 14)) (A : Finset (Region k)) :
    (A.biUnion fun U => venn S U.1).card = ∑ U ∈ A, (regionCount S U : ℕ) := by
  classical
  change (A.biUnion fun U => venn S U.1).card = ∑ U ∈ A, (venn S U.1).card
  apply Finset.card_biUnion
  intro U _hU V _hV hne
  exact distinct_regions_disjoint S U V hne

theorem total_region_count_le {k : ℕ} (S : Fin k → Finset (Fin 14)) :
    (∑ U : Region k, (regionCount S U : ℕ)) ≤ 14 := by
  classical
  calc
    (∑ U : Region k, (regionCount S U : ℕ)) =
        ((Finset.univ : Finset (Region k)).biUnion fun U => venn S U.1).card :=
      (region_union_card S Finset.univ).symm
    _ ≤ 14 := by
      simpa only [Fintype.card_fin] using
        ((Finset.univ : Finset (Region k)).biUnion fun U => venn S U.1).card_le_univ

/-- The regions containing index i partition exactly the ith monomial's variable set. -/
theorem member_regions_union {k : ℕ} (S : Fin k → Finset (Fin 14)) (i : Fin k) :
    ((memberRegions i).biUnion fun U => venn S U.1) = S i := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨U, hU, hjU⟩ := Finset.mem_biUnion.mp hj
    have hiU : i ∈ U.1 := (Finset.mem_filter.mp hU).2
    exact ((mem_venn_region S U.1 j).mp hjU i).mpr hiU
  · intro hj
    let U : Region k := ⟨pattern S j, ⟨i, (mem_pattern S j i).mpr hj⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨U, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (mem_pattern S j i).mpr hj⟩
    · apply (mem_venn_region S U.1 j).mpr
      intro l
      exact (mem_pattern S j l).symm

theorem member_region_count_eq {k : ℕ} (S : Fin k → Finset (Fin 14)) (i : Fin k) :
    (∑ U ∈ memberRegions i, (regionCount S U : ℕ)) = (S i).card := by
  exact (region_union_card S (memberRegions i)).symm.trans
    (congrArg Finset.card (member_regions_union S i))

/-- The constructed vector is a member of the exact frozen vennVectors definition. -/
theorem regionCount_mem_vennVectors {k : ℕ} (S : Fin k → Finset (Fin 14))
    (hS : ∀ i, (S i).card ≤ 7) : regionCount S ∈ vennVectors k := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, total_region_count_le S, ?_⟩
  intro i
  change (∑ U ∈ memberRegions i, (regionCount S U : ℕ)) ≤ 7
  rw [member_region_count_eq]
  exact hS i

/-- Any selected variable union is exactly the union of the nonempty regions meeting its indices. -/
theorem selected_union_regions {k : ℕ} (S : Fin k → Finset (Fin 14)) (T : Finset (Fin k)) :
    T.biUnion S = (meetingRegions T).biUnion (fun U => venn S U.1) := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, hiT, hji⟩ := Finset.mem_biUnion.mp hj
    let U : Region k := ⟨pattern S j, ⟨i, (mem_pattern S j i).mpr hji⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨U, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        ⟨i, Finset.mem_inter.mpr ⟨hiT, (mem_pattern S j i).mpr hji⟩⟩⟩
    · apply (mem_venn_region S U.1 j).mpr
      intro l
      exact (mem_pattern S j l).symm
  · intro hj
    obtain ⟨U, hU, hjU⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hU).2
    have hi' := Finset.mem_inter.mp hi
    exact Finset.mem_biUnion.mpr
      ⟨i, hi'.1, ((mem_venn_region S U.1 j).mp hjU i).mpr hi'.2⟩

/-- Union cardinality computed from a Venn vector, for use in the executable weight formula. -/
def unionCount {k : ℕ} (n : Region k → Fin 15) (T : Finset (Fin k)) : ℕ :=
  ∑ U ∈ meetingRegions T, (n U : ℕ)

theorem union_card_eq_unionCount {k : ℕ} (S : Fin k → Finset (Fin 14)) (T : Finset (Fin k)) :
    (T.biUnion S).card = unionCount (regionCount S) T := by
  rw [selected_union_regions]
  exact region_union_card S (meetingRegions T)

/-- The integer inclusion-exclusion formula on abstract finite Venn data. -/
def vennWeight (k : ℕ) (n : Region k → Fin 15) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.Nonempty),
    (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (14 - unionCount n T)

theorem family_weight_eq_vennWeight {k : ℕ} (S : Fin k → Finset (Fin 14)) :
    (hammingNorm (fun x : Pt 14 => ∑ i, ∏ j ∈ S i, x j) : ℤ) =
      vennWeight k (regionCount S) := by
  classical
  rw [Paper6InclusionExclusion.check_Lem21 14 k S]
  unfold vennWeight
  apply Finset.sum_congr rfl
  intro T _hT
  rw [union_card_eq_unionCount]

/-- The zero-term boundary needs no numerical certificate. -/
theorem empty_family_vennWeight (n : Region 0 → Fin 15) : vennWeight 0 n = 0 := by
  classical
  unfold vennWeight
  apply Finset.sum_eq_zero
  intro T hT
  obtain ⟨i, _hi⟩ := (Finset.mem_filter.mp hT).2
  exact Fin.elim0 i

/-- Full semantic reduction for arbitrary polynomial exponents, including constants and repeated supports.
The affine clause is equality of actual Hamming weights, not an extra certificate assumption. -/
theorem sparse_polynomial_has_venn_data (p : MvPolynomial (Fin 14) (ZMod 2))
    (hterms : p.support.card ≤ 5) (hdegree : p.totalDegree ≤ 7) :
    ∃ k ≤ 5, ∃ n ∈ vennVectors k,
      (hammingNorm (evalFun p) : ℤ) = vennWeight k n ∧
      (∀ φ : Pt 14 ≃ᵃ[ZMod 2] Pt 14,
        (hammingNorm (fun x => evalFun p (φ x)) : ℤ) = vennWeight k n) := by
  let S := Paper6Divisibility.monomialFamily p
  have hS : ∀ i, (S i).card ≤ 7 :=
    fun i => (Paper6Divisibility.monomialFamily_card_le p i).trans hdegree
  have hweight : (hammingNorm (evalFun p) : ℤ) =
      vennWeight p.support.card (regionCount S) := by
    rw [Paper6Divisibility.evalFun_eq_monomialFamily]
    exact family_weight_eq_vennWeight S
  refine ⟨p.support.card, hterms, regionCount S, regionCount_mem_vennVectors S hS, hweight, ?_⟩
  intro φ
  rw [Paper6AffineInvariance.weight_precomposition]
  exact hweight

/-- A small exact boundary calculation only; this is not the five-part PropE_counts contract. -/
theorem vennVectors_one_card : (vennVectors 1).card = 8 := by
  decide +kernel

end Paper6FiveMonomials

#print axioms Paper6FiveMonomials.Region
#print axioms Paper6FiveMonomials.regionCount
#print axioms Paper6FiveMonomials.memberRegions
#print axioms Paper6FiveMonomials.meetingRegions
#print axioms Paper6FiveMonomials.distinct_regions_disjoint
#print axioms Paper6FiveMonomials.region_union_card
#print axioms Paper6FiveMonomials.total_region_count_le
#print axioms Paper6FiveMonomials.member_regions_union
#print axioms Paper6FiveMonomials.member_region_count_eq
#print axioms Paper6FiveMonomials.regionCount_mem_vennVectors
#print axioms Paper6FiveMonomials.selected_union_regions
#print axioms Paper6FiveMonomials.unionCount
#print axioms Paper6FiveMonomials.union_card_eq_unionCount
#print axioms Paper6FiveMonomials.vennWeight
#print axioms Paper6FiveMonomials.family_weight_eq_vennWeight
#print axioms Paper6FiveMonomials.empty_family_vennWeight
#print axioms Paper6FiveMonomials.sparse_polynomial_has_venn_data
#print axioms Paper6FiveMonomials.vennVectors_one_card
