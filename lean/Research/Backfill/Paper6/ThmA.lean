import Research.Backfill.Paper6.ChallengeV3
import Research.RM714Weights

/-!
# Paper 6, frozen V3 Theorem A: explicit sparse polynomials

This proof targets the frozen `BackfillPaper6.V3.ThmA`, including both
`totalDegree <= 7` and `support.card <= 7`. The old existence-only interface
`RM714.IsRM714Weight` does not contain a support bound and is not used as a
substitute for this stronger target. The concrete old mask data and its generic
bit-count bridge are reused; the 17 concrete bit-count equations are separately
named and checked by the kernel in this new module.

Contract: statements-v3/FROZEN.json, SHA-256
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
-/

set_option autoImplicit false

namespace Paper6ThmA

open BackfillPaper6.V3

/-- The polynomial list encoding and the old list evaluation agree pointwise. -/
theorem evalFun_polyOf_eq (L : List (Finset (Fin 14))) :
    evalFun (polyOf L) = RM714.evalPoly L := by
  funext x
  simp only [evalFun, polyOf, RM714.evalPoly, map_list_sum,
    List.map_map, Function.comp_def,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]

/-- A squarefree product has degree at most the number of variables in it. -/
theorem monomial_degree_le {m : ℕ} (S : Finset (Fin m)) :
    (∏ i ∈ S, (MvPolynomial.X i :
      MvPolynomial (Fin m) (ZMod 2))).totalDegree ≤ S.card := by
  classical
  simpa using
    (MvPolynomial.totalDegree_finsetProd S
      (fun i => (MvPolynomial.X i :
        MvPolynomial (Fin m) (ZMod 2))))

/-- A sum preserves a common degree bound on its summands. -/
theorem polyOf_degree_le {m : ℕ}
    (L : List (Finset (Fin m))) (r : ℕ) :
    (∀ S ∈ L, S.card ≤ r) → (polyOf L).totalDegree ≤ r := by
  induction L with
  | nil =>
      intro h
      simp [polyOf]
  | cons S L ih =>
      intro h
      change
        ((∏ i ∈ S, (MvPolynomial.X i :
          MvPolynomial (Fin m) (ZMod 2))) +
          polyOf L).totalDegree ≤ r
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le
          ((monomial_degree_le S).trans (h S List.mem_cons_self))
          (ih (fun T hT => h T (List.mem_cons_of_mem S hT))))

/-- In particular the degree is bounded by the largest variable-set cardinality. -/
theorem polyOf_degree_le_max {m : ℕ}
    (L : List (Finset (Fin m))) :
    (polyOf L).totalDegree ≤ L.toFinset.sup Finset.card := by
  apply polyOf_degree_le
  intro S hS
  exact Finset.le_sup (f := Finset.card) (List.mem_toFinset.mpr hS)

/-- A product of variables has a single exponent vector, so at most one term. -/
theorem monomial_support_card_le {m : ℕ} (S : Finset (Fin m)) :
    (∏ i ∈ S, (MvPolynomial.X i :
      MvPolynomial (Fin m) (ZMod 2))).support.card ≤ 1 := by
  classical
  let d : Fin m →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1
  have hm :
      (∏ i ∈ S, (MvPolynomial.X i :
        MvPolynomial (Fin m) (ZMod 2))) =
        MvPolynomial.monomial d 1 := by
    dsimp [d]
    simpa only [MvPolynomial.X] using
      (MvPolynomial.monomial_sum_one (R := ZMod 2) S
        (fun i => Finsupp.single i 1)).symm
  rw [hm]
  simpa only [Finset.card_singleton] using
    (Finset.card_le_card
      (MvPolynomial.support_monomial_subset
        (s := d) (a := (1 : ZMod 2))))

/-- Cancellation or repeated monomials cannot increase the number of terms. -/
theorem polyOf_support_card_le {m : ℕ}
    (L : List (Finset (Fin m))) :
    (polyOf L).support.card ≤ L.length := by
  classical
  induction L with
  | nil => simp [polyOf]
  | cons S L ih =>
      change
        ((∏ i ∈ S, (MvPolynomial.X i :
          MvPolynomial (Fin m) (ZMod 2))) +
          polyOf L).support.card ≤ L.length + 1
      calc
        _ ≤
            (∏ i ∈ S, (MvPolynomial.X i :
              MvPolynomial (Fin m) (ZMod 2))).support.card +
            (polyOf L).support.card :=
          (Finset.card_le_card MvPolynomial.support_add).trans
            (Finset.card_union_le _ _)
        _ ≤ 1 + L.length :=
          Nat.add_le_add (monomial_support_card_le S) ih
        _ = L.length + 1 := Nat.add_comm _ _

/-- Over the binary field, counting nonzero values is counting values equal to one. -/
theorem hammingNorm_polyOf_eq_weight
    (L : List (Finset (Fin 14))) :
    hammingNorm (evalFun (polyOf L)) = RM714.weight L := by
  classical
  have hz : ∀ z : ZMod 2, z ≠ 0 ↔ z = 1 := by decide
  rw [evalFun_polyOf_eq]
  unfold hammingNorm RM714.weight
  congr 1
  exact Finset.filter_congr (fun x _ => hz _)

/-- A bounded mask list gives the full sparse-polynomial conclusion of Theorem A. -/
theorem concrete_witness
    (L : List ℕ) (w : ℕ)
    (hmask : ∀ s ∈ L, s < 2 ^ 14)
    (hdeg : L.all (fun s => decide (RM714.degNat s ≤ 7)) = true)
    (hlen : L.length ≤ 7)
    (hw : RM714.weightNat L = w) :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = w := by
  refine ⟨polyOf (L.map RM714.maskSet), ?_, ?_, ?_⟩
  · apply polyOf_degree_le
    intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
    have hd := List.all_eq_true.mp hdeg s hs
    rw [RM714.card_maskSet]
    simpa using hd
  · exact (polyOf_support_card_le _).trans
      (by simpa only [List.length_map] using hlen)
  · rw [hammingNorm_polyOf_eq_weight,
      RM714.weight_map_maskSet L hmask, hw]

/-! Each concrete enumeration is proved once here and reused by name. -/

theorem weightNat_354 : RM714.weightNat RM714.L354 = 354 := by
  decide +kernel

theorem witness_354 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 354 :=
  concrete_witness RM714.L354 354
    (by decide) (by decide +kernel) (by decide) weightNat_354

theorem weightNat_4378 : RM714.weightNat RM714.L4378 = 4378 := by
  decide +kernel

theorem witness_4378 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 4378 :=
  concrete_witness RM714.L4378 4378
    (by decide) (by decide +kernel) (by decide) weightNat_4378

theorem weightNat_4380 : RM714.weightNat RM714.L4380 = 4380 := by
  decide +kernel

theorem witness_4380 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 4380 :=
  concrete_witness RM714.L4380 4380
    (by decide) (by decide +kernel) (by decide) weightNat_4380

theorem weightNat_4382 : RM714.weightNat RM714.L4382 = 4382 := by
  decide +kernel

theorem witness_4382 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 4382 :=
  concrete_witness RM714.L4382 4382
    (by decide) (by decide +kernel) (by decide) weightNat_4382

theorem weightNat_8174 : RM714.weightNat RM714.L8174 = 8174 := by
  decide +kernel

theorem witness_8174 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8174 :=
  concrete_witness RM714.L8174 8174
    (by decide) (by decide +kernel) (by decide) weightNat_8174

theorem weightNat_8178 : RM714.weightNat RM714.L8178 = 8178 := by
  decide +kernel

theorem witness_8178 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8178 :=
  concrete_witness RM714.L8178 8178
    (by decide) (by decide +kernel) (by decide) weightNat_8178

theorem weightNat_8182 : RM714.weightNat RM714.L8182 = 8182 := by
  decide +kernel

theorem witness_8182 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8182 :=
  concrete_witness RM714.L8182 8182
    (by decide) (by decide +kernel) (by decide) weightNat_8182

theorem weightNat_8186 : RM714.weightNat RM714.L8186 = 8186 := by
  decide +kernel

theorem witness_8186 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8186 :=
  concrete_witness RM714.L8186 8186
    (by decide) (by decide +kernel) (by decide) weightNat_8186

theorem weightNat_8188 : RM714.weightNat RM714.L8188 = 8188 := by
  decide +kernel

theorem witness_8188 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8188 :=
  concrete_witness RM714.L8188 8188
    (by decide) (by decide +kernel) (by decide) weightNat_8188

theorem weightNat_8190 : RM714.weightNat RM714.L8190 = 8190 := by
  decide +kernel

theorem witness_8190 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8190 :=
  concrete_witness RM714.L8190 8190
    (by decide) (by decide +kernel) (by decide) weightNat_8190

theorem weightNat_8194 : RM714.weightNat RM714.L8194 = 8194 := by
  decide +kernel

theorem witness_8194 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8194 :=
  concrete_witness RM714.L8194 8194
    (by decide) (by decide +kernel) (by decide) weightNat_8194

theorem weightNat_8196 : RM714.weightNat RM714.L8196 = 8196 := by
  decide +kernel

theorem witness_8196 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8196 :=
  concrete_witness RM714.L8196 8196
    (by decide) (by decide +kernel) (by decide) weightNat_8196

theorem weightNat_8198 : RM714.weightNat RM714.L8198 = 8198 := by
  decide +kernel

theorem witness_8198 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8198 :=
  concrete_witness RM714.L8198 8198
    (by decide) (by decide +kernel) (by decide) weightNat_8198

theorem weightNat_8202 : RM714.weightNat RM714.L8202 = 8202 := by
  decide +kernel

theorem witness_8202 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8202 :=
  concrete_witness RM714.L8202 8202
    (by decide) (by decide +kernel) (by decide) weightNat_8202

theorem weightNat_8206 : RM714.weightNat RM714.L8206 = 8206 := by
  decide +kernel

theorem witness_8206 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8206 :=
  concrete_witness RM714.L8206 8206
    (by decide) (by decide +kernel) (by decide) weightNat_8206

theorem weightNat_8210 : RM714.weightNat RM714.L8210 = 8210 := by
  decide +kernel

theorem witness_8210 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 8210 :=
  concrete_witness RM714.L8210 8210
    (by decide) (by decide +kernel) (by decide) weightNat_8210

theorem weightNat_16030 : RM714.weightNat RM714.L16030 = 16030 := by
  decide +kernel

theorem witness_16030 :
    ∃ p : MvPolynomial (Fin 14) (ZMod 2),
      p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (evalFun p) = 16030 :=
  concrete_witness RM714.L16030 16030
    (by decide) (by decide +kernel) (by decide) weightNat_16030

/-- The exact frozen V3 Theorem A, with all seventeen members covered. -/
theorem thmA : BackfillPaper6.V3.ThmA := by
  intro w hw
  simp only [thmAWeights, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_354
  · exact witness_4378
  · exact witness_4380
  · exact witness_4382
  · exact witness_8174
  · exact witness_8178
  · exact witness_8182
  · exact witness_8186
  · exact witness_8188
  · exact witness_8190
  · exact witness_8194
  · exact witness_8196
  · exact witness_8198
  · exact witness_8202
  · exact witness_8206
  · exact witness_8210
  · exact witness_16030

/-- The same result with the custom evaluation and weight-set abbreviations unfolded. -/
theorem thmA_mathlib : BackfillPaper6.V3.ThmA_mathlib := by
  change BackfillPaper6.V3.ThmA
  exact thmA

end Paper6ThmA

#print axioms Paper6ThmA.evalFun_polyOf_eq
#print axioms Paper6ThmA.monomial_degree_le
#print axioms Paper6ThmA.polyOf_degree_le
#print axioms Paper6ThmA.polyOf_degree_le_max
#print axioms Paper6ThmA.monomial_support_card_le
#print axioms Paper6ThmA.polyOf_support_card_le
#print axioms Paper6ThmA.hammingNorm_polyOf_eq_weight
#print axioms Paper6ThmA.concrete_witness
#print axioms Paper6ThmA.weightNat_354
#print axioms Paper6ThmA.witness_354
#print axioms Paper6ThmA.weightNat_4378
#print axioms Paper6ThmA.witness_4378
#print axioms Paper6ThmA.weightNat_4380
#print axioms Paper6ThmA.witness_4380
#print axioms Paper6ThmA.weightNat_4382
#print axioms Paper6ThmA.witness_4382
#print axioms Paper6ThmA.weightNat_8174
#print axioms Paper6ThmA.witness_8174
#print axioms Paper6ThmA.weightNat_8178
#print axioms Paper6ThmA.witness_8178
#print axioms Paper6ThmA.weightNat_8182
#print axioms Paper6ThmA.witness_8182
#print axioms Paper6ThmA.weightNat_8186
#print axioms Paper6ThmA.witness_8186
#print axioms Paper6ThmA.weightNat_8188
#print axioms Paper6ThmA.witness_8188
#print axioms Paper6ThmA.weightNat_8190
#print axioms Paper6ThmA.witness_8190
#print axioms Paper6ThmA.weightNat_8194
#print axioms Paper6ThmA.witness_8194
#print axioms Paper6ThmA.weightNat_8196
#print axioms Paper6ThmA.witness_8196
#print axioms Paper6ThmA.weightNat_8198
#print axioms Paper6ThmA.witness_8198
#print axioms Paper6ThmA.weightNat_8202
#print axioms Paper6ThmA.witness_8202
#print axioms Paper6ThmA.weightNat_8206
#print axioms Paper6ThmA.witness_8206
#print axioms Paper6ThmA.weightNat_8210
#print axioms Paper6ThmA.witness_8210
#print axioms Paper6ThmA.weightNat_16030
#print axioms Paper6ThmA.witness_16030
#print axioms Paper6ThmA.thmA
#print axioms Paper6ThmA.thmA_mathlib
