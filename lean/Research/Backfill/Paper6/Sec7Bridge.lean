import Research.Backfill.Paper6.BridgeChallenge
import Research.Backfill.Paper6.ThmA

/-!
# The actual released RM714 model and the frozen Mathlib model are equivalent

Complete source candidate for the frozen `BackfillPaper6.V3.Sec7Bridge`.
Compilation, dependency audit, and acceptance are pending root-controlled verification.

The reverse direction starts with any genuine polynomial of total degree at most
seven. Its nonzero binary coefficients are one; every positive power has the same
evaluation as its variable. Replacing each exponent vector by its actual support
therefore gives a finite list with the same truth table, with every set of variables
of cardinality at most seven. Equal resulting supports are deliberately not deduplicated:
they cancel in the binary sum exactly as required.

No spectrum assertion, classification, witness bank, or unproved bridge is assumed.
-/

set_option autoImplicit false

namespace Paper6ReleasedModelBridge

open BackfillPaper6.V3

/-- Every nonzero coefficient of a binary polynomial is exactly one. -/
theorem coefficient_one {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2))
    (d : Fin m →₀ ℕ) (hd : d ∈ p.support) : p.coeff d = 1 := by
  have hbinary : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  exact hbinary _ (MvPolynomial.mem_support_iff.mp hd)

/-- Exponents remain arbitrary positive natural numbers, not only zero or one. -/
theorem binary_positive_power (z : ZMod 2) (n : ℕ) (hn : n ≠ 0) : z ^ n = z := by
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hbinary z with rfl | rfl
  · simp [hn]
  · simp

/-- Squarefree reduction of a monomial cannot increase its degree. -/
theorem exponent_support_card_le {m : ℕ} (d : Fin m →₀ ℕ) :
    d.support.card ≤ d.sum (fun _ n => n) := by
  classical
  calc
    d.support.card = ∑ _i ∈ d.support, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = d.sum (fun _ n => n) := rfl

/-- One list entry per actual nonzero polynomial coefficient. -/
noncomputable def squarefreeList {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) :
    List (Finset (Fin m)) :=
  p.support.toList.map (fun d => d.support)

theorem squarefreeList_degree {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2))
    (r : ℕ) (hp : p.totalDegree ≤ r) :
    ∀ S ∈ squarefreeList p, S.card ≤ r := by
  classical
  intro S hS
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hS
  have hd' : d ∈ p.support := by simpa only [Finset.mem_toList] using hd
  exact (exponent_support_card_le d).trans ((MvPolynomial.le_totalDegree hd').trans hp)

/-- Pointwise equality with the real released list evaluator, not a new predicate. -/
theorem evalPoly_squarefreeList (p : MvPolynomial (Fin 14) (ZMod 2)) :
    RM714.evalPoly (squarefreeList p) = evalFun p := by
  classical
  funext x
  simp only [squarefreeList, RM714.evalPoly, List.map_map, Function.comp_def,
    Finset.sum_map_toList, evalFun, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coefficient_one p d hd, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  exact (binary_positive_power (x i) (d i) (Finsupp.mem_support_iff.mp hi)).symm

/-- The released count of values equal to one is the actual Hamming weight. -/
theorem released_weight_eq_hammingNorm (L : List (Finset (Fin 14))) :
    RM714.weight L = hammingNorm (RM714.evalPoly L) := by
  have h := Paper6ThmA.hammingNorm_polyOf_eq_weight L
  rw [Paper6ThmA.evalFun_polyOf_eq] at h
  exact h.symm

theorem list_to_mathlib (w : ℕ) (h : RM714.IsRM714Weight w) : IsWeight 7 14 w := by
  rcases h with ⟨L, hdegree, hweight⟩
  refine ⟨evalFun (polyOf L), ⟨polyOf L,
    Paper6ThmA.polyOf_degree_le L 7 hdegree, rfl⟩, ?_⟩
  rw [Paper6ThmA.hammingNorm_polyOf_eq_weight]
  exact hweight

theorem mathlib_to_list (w : ℕ) (h : IsWeight 7 14 w) : RM714.IsRM714Weight w := by
  rcases h with ⟨f, ⟨p, hdegree, heval⟩, hweight⟩
  refine ⟨squarefreeList p, squarefreeList_degree p 7 hdegree, ?_⟩
  rw [released_weight_eq_hammingNorm, evalPoly_squarefreeList, ← heval]
  exact hweight

/-- Exactly the frozen, unconditional, bidirectional Section 7 interface. -/
theorem check_Sec7Bridge : BackfillPaper6.V3.Sec7Bridge := by
  intro w
  exact ⟨list_to_mathlib w, mathlib_to_list w⟩

end Paper6ReleasedModelBridge

#print axioms Paper6ReleasedModelBridge.coefficient_one
#print axioms Paper6ReleasedModelBridge.binary_positive_power
#print axioms Paper6ReleasedModelBridge.exponent_support_card_le
#print axioms Paper6ReleasedModelBridge.squarefreeList
#print axioms Paper6ReleasedModelBridge.squarefreeList_degree
#print axioms Paper6ReleasedModelBridge.evalPoly_squarefreeList
#print axioms Paper6ReleasedModelBridge.released_weight_eq_hammingNorm
#print axioms Paper6ReleasedModelBridge.list_to_mathlib
#print axioms Paper6ReleasedModelBridge.mathlib_to_list
#print axioms Paper6ReleasedModelBridge.check_Sec7Bridge
