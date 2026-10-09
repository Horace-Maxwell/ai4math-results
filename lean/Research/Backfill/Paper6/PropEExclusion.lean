import Research.Backfill.Paper6.PairChecked

/-!
# Complete Proposition E and the necessary direction of its retained interval remark

Source candidate only. Every numerical leaf is an actual kernel obligation in
the imported certificate modules. None has been executed by the source author.
The final statements do not assume a weight table, finite exclusion, or conjecture.
-/

set_option autoImplicit false

namespace Paper6FiveExclusion

open BackfillPaper6.V3

/-- The original polynomial's indexed terms are preserved through squarefree
evaluation, complementary-pair extraction, and the complete two-block checker. -/
theorem sparse_good_of_mod (p : MvPolynomial (Fin 14) (ZMod 2))
    (hterms : p.support.card ≤ 5) (hdegree : p.totalDegree ≤ 7)
    (hmod : hammingNorm (evalFun p) % 4 = 2) :
    GoodWeight (hammingNorm (evalFun p)) := by
  let S := Paper6Divisibility.monomialFamily p
  have hS : ∀ i, (S i).card ≤ 7 :=
    fun i => (Paper6Divisibility.monomialFamily_card_le p i).trans hdegree
  obtain ⟨i, j, hij, hA, hB, hd, hu⟩ :=
    Paper6FiveMonomials.polynomial_complementary_pair p hdegree hmod
  obtain ⟨q, hq, R, hR, heq⟩ := extract_pair S hterms hS i j hij
  have heval := Paper6Divisibility.evalFun_eq_monomialFamily p
  change evalFun p = (fun x : Pt 14 => ∑ a, ∏ b ∈ S a, x b) at heval
  rw [heval, heq]
  exact pair_good (S i) (S j) R hq hA hB hd hu hR

theorem sparse_exclusion (p : MvPolynomial (Fin 14) (ZMod 2))
    (hterms : p.support.card ≤ 5) (hdegree : p.totalDegree ≤ 7) :
    hammingNorm (evalFun p) ∉ U := by
  intro hw
  have hmod := Paper6FiveMonomials.u_mod_four _ hw
  exact (sparse_good_of_mod p hterms hdegree hmod).1 hw

/-- Exact necessary interval direction for the separate remark existence proof.
This does not assert existence of any interval weight. -/
theorem sparse_interval_upper (p : MvPolynomial (Fin 14) (ZMod 2))
    (hterms : p.support.card ≤ 5) (hdegree : p.totalDegree ≤ 7)
    (hmod : hammingNorm (evalFun p) % 4 = 2)
    (hlo : 250 ≤ hammingNorm (evalFun p)) (hhi : hammingNorm (evalFun p) ≤ 400) :
    hammingNorm (evalFun p) = 254 ∨ hammingNorm (evalFun p) = 314 ∨
      hammingNorm (evalFun p) = 318 ∨
        (hammingNorm (evalFun p) % 4 = 2 ∧ 338 ≤ hammingNorm (evalFun p) ∧
          hammingNorm (evalFun p) ≤ 398) :=
  (sparse_good_of_mod p hterms hdegree hmod).2 hmod hlo hhi

theorem interval_necessary (w : ℕ) (hw : w ∈ weightsLe5)
    (hmod : w % 4 = 2) (hlo : 250 ≤ w) (hhi : w ≤ 400) :
    w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398) := by
  obtain ⟨p, hterms, hdegree, rfl⟩ := hw
  exact sparse_interval_upper p hterms hdegree hmod hlo hhi

/-- Exact complete frozen contract, including every affine bijection. -/
theorem check_PropE : BackfillPaper6.V3.PropE := by
  constructor
  · exact sparse_exclusion
  · intro p hterms hdegree φ
    rw [Paper6AffineInvariance.weight_precomposition]
    exact sparse_exclusion p hterms hdegree

/-- Equivalent restatement only; not an additional mathematical result. -/
theorem check_PropE_mathlib : BackfillPaper6.V3.PropE_mathlib := sparse_exclusion

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.sparse_good_of_mod
#print axioms Paper6FiveExclusion.sparse_exclusion
#print axioms Paper6FiveExclusion.sparse_interval_upper
#print axioms Paper6FiveExclusion.interval_necessary
#print axioms Paper6FiveExclusion.check_PropE
#print axioms Paper6FiveExclusion.check_PropE_mathlib
