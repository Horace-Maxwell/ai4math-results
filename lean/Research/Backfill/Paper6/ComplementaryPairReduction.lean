import Research.Backfill.Paper6.VennBridge

/-!
# A mathematical compression for the remaining Proposition E certificates

Every bounded-degree monomial family of weight two modulo four contains two
disjoint degree-seven monomials covering all fourteen variables. This removes
the need to enumerate arbitrary 31-region configurations for the exclusion
problem. No remaining enumeration result is asserted by this module.
-/

set_option autoImplicit false

namespace Paper6FiveMonomials

open BackfillPaper6.V3

/-- Except for a two-term selection covering all variables, every inclusion-exclusion term
has at least two factors of two. -/
theorem inclusion_term_four_dvd {k : ℕ} (S : Fin k → Finset (Fin 14))
    (hS : ∀ i, (S i).card ≤ 7) (T : Finset (Fin k)) (hT : T.Nonempty)
    (hnot : T.card = 2 → (T.biUnion S).card ≠ 14) :
    (4 : ℤ) ∣ (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (14 - (T.biUnion S).card) := by
  classical
  have ht : 1 ≤ T.card := Finset.card_pos.mpr hT
  have hu : (T.biUnion S).card ≤ 14 := by
    simpa only [Fintype.card_fin] using (T.biUnion S).card_le_univ
  have htotal := Paper6Divisibility.union_card_le 14 k 7 S hS T
  have hexponent : 2 ≤ (T.card - 1) + (14 - (T.biUnion S).card) := by
    by_cases hlarge : 3 ≤ T.card
    · omega
    · have hsmall : T.card = 1 ∨ T.card = 2 := by omega
      rcases hsmall with hsmall | hsmall
      · rw [hsmall] at htotal
        omega
      · have hne := hnot hsmall
        omega
  have hfactor :
      (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (14 - (T.biUnion S).card) =
        (-1 : ℤ) ^ (T.card - 1) *
          (2 : ℤ) ^ ((T.card - 1) + (14 - (T.biUnion S).card)) := by
    rw [neg_pow, pow_add]
    ring
  rw [hfactor]
  have hpow : (4 : ℤ) ∣ (2 : ℤ) ^ ((T.card - 1) + (14 - (T.biUnion S).card)) := by
    simpa using pow_dvd_pow (2 : ℤ) hexponent
  exact dvd_mul_of_dvd_right hpow _

/-- A word of weight two modulo four must have a two-element selection covering all variables. -/
theorem exists_covering_pair {k : ℕ} (S : Fin k → Finset (Fin 14))
    (hS : ∀ i, (S i).card ≤ 7)
    (hmod : hammingNorm (fun x : Pt 14 => ∑ i, ∏ j ∈ S i, x j) % 4 = 2) :
    ∃ T : Finset (Fin k), T.card = 2 ∧ (T.biUnion S).card = 14 := by
  classical
  by_contra hnone
  have hnot (T : Finset (Fin k)) (hcard : T.card = 2) : (T.biUnion S).card ≠ 14 := by
    intro hu
    exact hnone ⟨T, hcard, hu⟩
  have hdivZ : (4 : ℤ) ∣
      (hammingNorm (fun x : Pt 14 => ∑ i, ∏ j ∈ S i, x j) : ℤ) := by
    rw [Paper6InclusionExclusion.check_Lem21 14 k S]
    apply Finset.dvd_sum
    intro T hT
    exact inclusion_term_four_dvd S hS T (Finset.mem_filter.mp hT).2 (hnot T)
  have hdiv : (4 : ℕ) ∣ hammingNorm (fun x : Pt 14 => ∑ i, ∏ j ∈ S i, x j) := by
    exact_mod_cast hdivZ
  have hzero := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- The degree bound forces the covering pair to be two disjoint seven-element sets. -/
theorem complementary_pair_of_weight_two_mod_four {k : ℕ}
    (S : Fin k → Finset (Fin 14)) (hS : ∀ i, (S i).card ≤ 7)
    (hmod : hammingNorm (fun x : Pt 14 => ∑ i, ∏ j ∈ S i, x j) % 4 = 2) :
    ∃ i j : Fin k, i ≠ j ∧ (S i).card = 7 ∧ (S j).card = 7 ∧
      Disjoint (S i) (S j) ∧ S i ∪ S j = Finset.univ := by
  classical
  obtain ⟨T, hcard, hu⟩ := exists_covering_pair S hS hmod
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hcard
  rw [hT, Finset.biUnion_insert, Finset.singleton_biUnion] at hu
  have hi := hS i
  have hj := hS j
  have hcount := Finset.card_union_add_card_inter (S i) (S j)
  have hi7 : (S i).card = 7 := by omega
  have hj7 : (S j).card = 7 := by omega
  have hzero : (S i ∩ S j).card = 0 := by omega
  refine ⟨i, j, hij, hi7, hj7, ?_, ?_⟩
  · exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  · apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin] using hu

/-- The same compression applies to arbitrary exponent vectors in actual polynomials. -/
theorem polynomial_complementary_pair (p : MvPolynomial (Fin 14) (ZMod 2))
    (hdegree : p.totalDegree ≤ 7) (hmod : hammingNorm (evalFun p) % 4 = 2) :
    ∃ i j : Fin p.support.card, i ≠ j ∧
      (Paper6Divisibility.monomialFamily p i).card = 7 ∧
      (Paper6Divisibility.monomialFamily p j).card = 7 ∧
      Disjoint (Paper6Divisibility.monomialFamily p i) (Paper6Divisibility.monomialFamily p j) ∧
      Paper6Divisibility.monomialFamily p i ∪ Paper6Divisibility.monomialFamily p j = Finset.univ := by
  have hS : ∀ i, (Paper6Divisibility.monomialFamily p i).card ≤ 7 :=
    fun i => (Paper6Divisibility.monomialFamily_card_le p i).trans hdegree
  rw [Paper6Divisibility.evalFun_eq_monomialFamily] at hmod
  exact complementary_pair_of_weight_two_mod_four (Paper6Divisibility.monomialFamily p) hS hmod

theorem u_mod_four : ∀ w ∈ U, w % 4 = 2 := by decide +kernel

/-- In particular every potential PropE counterexample has the complementary pair above. -/
theorem polynomial_U_complementary_pair (p : MvPolynomial (Fin 14) (ZMod 2))
    (hdegree : p.totalDegree ≤ 7) (hw : hammingNorm (evalFun p) ∈ U) :
    ∃ i j : Fin p.support.card, i ≠ j ∧
      (Paper6Divisibility.monomialFamily p i).card = 7 ∧
      (Paper6Divisibility.monomialFamily p j).card = 7 ∧
      Disjoint (Paper6Divisibility.monomialFamily p i) (Paper6Divisibility.monomialFamily p j) ∧
      Paper6Divisibility.monomialFamily p i ∪ Paper6Divisibility.monomialFamily p j = Finset.univ :=
  polynomial_complementary_pair p hdegree (u_mod_four _ hw)

end Paper6FiveMonomials

#print axioms Paper6FiveMonomials.inclusion_term_four_dvd
#print axioms Paper6FiveMonomials.exists_covering_pair
#print axioms Paper6FiveMonomials.complementary_pair_of_weight_two_mod_four
#print axioms Paper6FiveMonomials.polynomial_complementary_pair
#print axioms Paper6FiveMonomials.u_mod_four
#print axioms Paper6FiveMonomials.polynomial_U_complementary_pair
#print Paper6FiveMonomials.sparse_polynomial_has_venn_data
#print Paper6FiveMonomials.polynomial_complementary_pair
