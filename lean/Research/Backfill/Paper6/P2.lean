import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.InclusionExclusion

/-!
# Paper 6 V3: the full binary Reed–Muller weight divisibility theorem

Every polynomial over ZMod 2 is converted, as a function, to an indexed family
of squarefree monomials by keeping the supports of its nonzero terms. Repeated
variable sets are allowed. Each set has cardinality bounded by total degree.
The accepted inclusion–exclusion formula then expresses the integer weight as
a sum whose individual terms are all divisible by 2^((m-1)/r).

The arithmetic argument retains natural subtraction and covers m = 0, all
positive orders r, and the empty monomial family. No condition r < m is added.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Candidate source only; compilation and acceptance are controlled by the root.
-/

set_option autoImplicit false

namespace Paper6Divisibility

open BackfillPaper6.V3

/-- A positive power of a binary value is the value itself. -/
theorem binary_pow_of_ne_zero (z : ZMod 2) (n : ℕ) (hn : n ≠ 0) : z ^ n = z := by
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hbit z with rfl | rfl <;> simp [hn]

/-- The number of nonzero exponents is no larger than their total sum. -/
theorem exponent_support_card_le {m : ℕ} (d : Fin m →₀ ℕ) :
    d.support.card ≤ d.sum (fun _ e => e) := by
  classical
  calc
    d.support.card = ∑ _i ∈ d.support, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      have hnonzero : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      omega
    _ = d.sum (fun _ e => e) := rfl

/-- The variable support of an actual nonzero polynomial term obeys the polynomial's degree bound. -/
theorem support_card_le_totalDegree {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) {d : Fin m →₀ ℕ} (hd : d ∈ p.support) :
    d.support.card ≤ p.totalDegree :=
  (exponent_support_card_le d).trans (MvPolynomial.le_totalDegree hd)

/-- Polynomial evaluation over the binary field can discard all positive exponent magnitudes. -/
theorem eval_eq_squarefree_sum {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) (x : Pt m) :
    evalFun p x = ∑ d ∈ p.support, ∏ j ∈ d.support, x j := by
  classical
  change MvPolynomial.eval x p = _
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d hd
  have hbit : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hcoeff : p.coeff d = 1 := hbit _ (MvPolynomial.mem_support_iff.mp hd)
  rw [hcoeff, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  exact binary_pow_of_ne_zero (x i) (d i) (Finsupp.mem_support_iff.mp hi)

/-- An indexed squarefree family with one entry for every original nonzero term.
Different exponent vectors may produce the same variable set; the family retains both entries. -/
noncomputable def monomialFamily {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) : Fin p.support.card → Finset (Fin m) :=
  fun i => (p.support.equivFin.symm i).val.support

/-- Each family member satisfies the original total-degree bound. -/
theorem monomialFamily_card_le {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) (i : Fin p.support.card) :
    (monomialFamily p i).card ≤ p.totalDegree := by
  classical
  exact support_card_le_totalDegree p (p.support.equivFin.symm i).property

/-- Exact function-level bridge to the arbitrary-family inclusion–exclusion interface. -/
theorem evalFun_eq_monomialFamily {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) :
    evalFun p = fun x : Pt m => ∑ i : Fin p.support.card, ∏ j ∈ monomialFamily p i, x j := by
  classical
  funext x
  calc
    evalFun p x = ∑ d ∈ p.support, ∏ j ∈ d.support, x j := eval_eq_squarefree_sum p x
    _ = ∑ d : p.support, ∏ j ∈ d.val.support, x j :=
      (Finset.sum_coe_sort p.support (fun d : Fin m →₀ ℕ => ∏ j ∈ d.support, x j)).symm
    _ = ∑ i : Fin p.support.card, ∏ j ∈ monomialFamily p i, x j := by
      refine Fintype.sum_equiv p.support.equivFin
        (fun d : p.support => ∏ j ∈ d.val.support, x j)
        (fun i : Fin p.support.card => ∏ j ∈ monomialFamily p i, x j) ?_
      intro d
      unfold monomialFamily
      rw [Equiv.symm_apply_apply]

/-- The exponent forced by a nonempty choice of monomials is at least the McEliece exponent.
The hypotheses on u are the ambient bound and the union bound; natural subtraction is retained. -/
theorem exponent_lower_bound (r m k u : ℕ)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (hum : u ≤ m) (hur : u ≤ r * k) :
    (m - 1) / r ≤ k - 1 + (m - u) := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hscale : m - u ≤ (m - u) * r := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m - u) hr
    have hstrict : m - 1 < (k + (m - u)) * r := by
      calc
        m - 1 < m := by omega
        _ = u + (m - u) := by omega
        _ ≤ r * k + (m - u) * r := Nat.add_le_add hur hscale
        _ = (k + (m - u)) * r := by ring
    have hdiv : (m - 1) / r < k + (m - u) :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr hstrict
    omega

/-- The selected variable union has at most r times the number of selected monomials. -/
theorem union_card_le (m k r : ℕ) (S : Fin k → Finset (Fin m))
    (hS : ∀ i, (S i).card ≤ r) (T : Finset (Fin k)) :
    (T.biUnion S).card ≤ r * T.card := by
  classical
  calc
    (T.biUnion S).card ≤ ∑ i ∈ T, (S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, r := Finset.sum_le_sum (fun i _hi => hS i)
    _ = r * T.card := by simp [Nat.mul_comm]

/-- Each integer term of the inclusion–exclusion formula has the required divisor. -/
theorem inclusion_term_dvd (r m k : ℕ) (hr : 1 ≤ r)
    (S : Fin k → Finset (Fin m)) (hS : ∀ i, (S i).card ≤ r)
    (T : Finset (Fin k)) (hT : T.Nonempty) :
    (2 : ℤ) ^ ((m - 1) / r) ∣
      (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (m - (T.biUnion S).card) := by
  classical
  have hambient : (T.biUnion S).card ≤ m := by
    simpa only [Fintype.card_fin] using (T.biUnion S).card_le_univ
  have hexponent := exponent_lower_bound r m T.card (T.biUnion S).card hr
    (Finset.card_pos.mpr hT) hambient (union_card_le m k r S hS T)
  have hfactor :
      (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (m - (T.biUnion S).card) =
      (-1 : ℤ) ^ (T.card - 1) *
        (2 : ℤ) ^ ((T.card - 1) + (m - (T.biUnion S).card)) := by
    rw [neg_pow, pow_add]
    ring
  rw [hfactor]
  exact dvd_mul_of_dvd_right (pow_dvd_pow (2 : ℤ) hexponent) _

/-- Full divisibility for arbitrary bounded-degree monomial families, including the empty family. -/
theorem monomialFamily_weight_dvd (r m k : ℕ) (hr : 1 ≤ r)
    (S : Fin k → Finset (Fin m)) (hS : ∀ i, (S i).card ≤ r) :
    (2 : ℕ) ^ ((m - 1) / r) ∣
      hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S i, x j) := by
  classical
  have hint : (2 : ℤ) ^ ((m - 1) / r) ∣
      (hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S i, x j) : ℤ) := by
    rw [Paper6InclusionExclusion.check_Lem21 m k S]
    apply Finset.dvd_sum
    intro T hT
    exact inclusion_term_dvd r m k hr S hS T (Finset.mem_filter.mp hT).2
  exact_mod_cast hint

/-- The complete arbitrary-order, arbitrary-dimension McEliece statement for the actual RM code. -/
theorem rm_weight_divisibility (r m : ℕ) (hr : 1 ≤ r)
    (f : BFun m) (hf : f ∈ RM r m) :
    2 ^ ((m - 1) / r) ∣ hammingNorm f := by
  rcases hf with ⟨p, hp, rfl⟩
  rw [evalFun_eq_monomialFamily]
  exact monomialFamily_weight_dvd r m p.support.card hr (monomialFamily p)
    (fun i => (monomialFamily_card_le p i).trans hp)

/-- The explicit RM(6,13) specialization retained in the frozen contract. -/
theorem rm613_four_dvd (h : BFun 13) (hh : h ∈ RM 6 13) : 4 ∣ hammingNorm h := by
  have hdiv := rm_weight_divisibility 6 13 (by decide) h hh
  norm_num at hdiv
  exact hdiv

/-- Both conjuncts of the unchanged frozen P2 contract. -/
theorem p2 : BackfillPaper6.V3.P2 :=
  ⟨rm_weight_divisibility, rm613_four_dvd⟩

/-- Exact contract check; the alias does not count as another mathematical result. -/
theorem check_P2 : BackfillPaper6.V3.P2 := p2

end Paper6Divisibility

#print axioms Paper6Divisibility.binary_pow_of_ne_zero
#print axioms Paper6Divisibility.exponent_support_card_le
#print axioms Paper6Divisibility.support_card_le_totalDegree
#print axioms Paper6Divisibility.eval_eq_squarefree_sum
#print axioms Paper6Divisibility.monomialFamily_card_le
#print axioms Paper6Divisibility.evalFun_eq_monomialFamily
#print axioms Paper6Divisibility.exponent_lower_bound
#print axioms Paper6Divisibility.union_card_le
#print axioms Paper6Divisibility.inclusion_term_dvd
#print axioms Paper6Divisibility.monomialFamily_weight_dvd
#print axioms Paper6Divisibility.rm_weight_divisibility
#print axioms Paper6Divisibility.rm613_four_dvd
#print axioms Paper6Divisibility.p2
#print axioms Paper6Divisibility.check_P2
#print Paper6Divisibility.check_P2
