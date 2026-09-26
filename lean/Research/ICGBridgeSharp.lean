import Research.ICGBridgeFinal

/-!
# Sharp energy gap for Roldán's Conjecture 1.3 (`q = 3`), at graph level

* `roldan_q3_gap` : for `p` prime, `p ≥ 5`, `D ⊆ properDivisors (27 p²)`, `D ≠ D*`,
  `energy(ICG(27p², D)) + 24 (p² - 2p + 2) ≤ energy(ICG(27p², D*))`.
* `roldan_q3_sharp` : `energy(ICG(27p², D* ∪ {3p²})) = 242 p² - 356 p + 154`
  `= energy(ICG(27p², D*)) - 24 (p² - 2p + 2)`, so the gap is attained
  (`roldan_q3_gap_attained`).
* the same statements for the mathlib `SimpleGraph.circulantGraph` model (`icgGraph`).

Arithmetic input: `CirculantQ3.exactEnergy_unique` and a single-mask kernel computation for the
mask `1957` of `D* ∪ {3p²}` (bit 9 = exponent pair `(2,1)`, i.e. the divisor `3p²`).
-/

namespace ICGBridge

/-! ### Arithmetic of the runner-up mask `1957` -/

set_option maxRecDepth 100000 in
theorem starPlus_same_sign : ∀ r : Fin 12,
    (∀ k : Fin 3, 0 ≤ CirculantQ3.coeff 1957 r k) ∨
      (∀ k : Fin 3, CirculantQ3.coeff 1957 r k ≤ 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem starPlus_upper : CirculantQ3.upper 1957 0 = 4424 ∧ CirculantQ3.upper 1957 1 = 2064 ∧
    CirculantQ3.upper 1957 2 = 242 := by
  decide +kernel

theorem energy_starPlus (x : ℤ) (hx : 0 ≤ x) :
    CirculantQ3.energy x 1957 = 4424 + 2064 * x + 242 * x ^ 2 := by
  have hs : CirculantQ3.energy x 1957 = CirculantQ3.upper 1957 0 +
      CirculantQ3.upper 1957 1 * x + CirculantQ3.upper 1957 2 * x ^ 2 := by
    unfold CirculantQ3.energy CirculantQ3.upper
    simp_rw [CirculantQ3.poly_abs_eq _ _ hx (starPlus_same_sign _)]
    simp only [Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs, starPlus_upper.1, starPlus_upper.2.1, starPlus_upper.2.2]

theorem exactEnergy_starPlus (p : ℤ) (hp : 5 ≤ p) :
    CirculantQ3.exactEnergy p 1957 = 242 * p ^ 2 - 356 * p + 154 := by
  have hx : 0 ≤ p - 5 := by omega
  have h := energy_starPlus (p - 5) hx
  have hs := CirculantQ3.exactEnergy_eq_energy (p - 5) 1957
  have heq : p - 5 + 5 = p := by ring
  rw [heq] at hs
  rw [← hs] at h
  rw [h]
  ring

/-! ### The connection set `D* ∪ {3p²}` and its mask -/

/-- Bit positions of `1957`: those of `D*` plus bit `9` (exponent pair `(2,1)`). -/
def starPlusBits : Finset (Fin 11) := {0, 2, 5, 7, 8, 9, 10}

lemma ej_nine (p : ℕ) : ej p 9 = 3 * p ^ 2 := by
  rw [show ej p 9 = p ^ 2 * 3 ^ 1 from rfl]
  ring

lemma DstarPlus_eq_image (p : ℕ) :
    insert (3 * p ^ 2) (Dstar p) = Finset.image (ej p) starPlusBits := by
  have h : starPlusBits = insert 9 starBits := by
    ext j
    fin_cases j <;> decide
  rw [Dstar_eq_image, h, Finset.image_insert, ej_nine]

lemma bitsOf_DstarPlus {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    bitsOf p (insert (3 * p ^ 2) (Dstar p)) = Copy.chosen 1957 := by
  funext j
  simp only [bitsOf, DstarPlus_eq_image, (ej_injective hp hp3).mem_finset_image]
  fin_cases j <;> decide

lemma maskOf_DstarPlus {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    maskOf p (insert (3 * p ^ 2) (Dstar p)) = 1957 := by
  apply chosen_injective
  simp only [chosen_maskOf, bitsOf_DstarPlus hp hp3]

lemma DstarPlus_subset (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    insert (3 * p ^ 2) (Dstar p) ⊆ (27 * p ^ 2).properDivisors := by
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · rw [Nat.mem_properDivisors]
    have := hp.pos
    exact ⟨⟨9, by ring⟩, by nlinarith⟩
  · exact Dstar_subset p hp5 hx

lemma DstarPlus_ne (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    insert (3 * p ^ 2) (Dstar p) ≠ Dstar p := by
  have hp3 : p ≠ 3 := by omega
  rw [Ne, Finset.insert_eq_self, Dstar_eq_image, ← ej_nine,
    (ej_injective hp hp3).mem_finset_image]
  decide

/-! ### Graph-level statements (adjacency-matrix model `icgAdj`) -/

/-- **Energy gap.** Every `D ≠ D*` loses at least `24 (p² - 2p + 2)`. -/
theorem roldan_q3_gap (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (D : Finset ℕ)
    (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) + 24 * ((p : ℝ) ^ 2 - 2 * p + 2) ≤
      energy (icgAdj (27 * p ^ 2) (Dstar p)) (icgAdj_isHermitian _ _) := by
  have hp3 : p ≠ 3 := by omega
  have hNot : ∀ E : Finset ℕ, E ⊆ (27 * p ^ 2).properDivisors → 27 * p ^ 2 ∉ E :=
    fun E hE hmem => lt_irrefl _ (Nat.mem_properDivisors.mp (hE hmem)).2
  have hm : maskOf p D ≠ CirculantQ3.star := by
    rw [← copy_star_eq]
    exact maskOf_ne_star hp hp5 hD hne
  have h := CirculantQ3.exactEnergy_unique p (by exact_mod_cast hp5) (maskOf p D) hm
  rw [energy_icgAdj_eq_exactEnergy p hp hp3 D (hNot D hD),
    energy_icgAdj_eq_exactEnergy p hp hp3 (Dstar p) (hNot _ (Dstar_subset p hp5)),
    maskOf_Dstar hp hp3, copy_star_eq]
  have h' : ((CirculantQ3.exactEnergy p (maskOf p D) + 24 * ((p : ℤ) ^ 2 - 2 * p + 2) : ℤ) : ℝ) ≤
      ((CirculantQ3.exactEnergy p CirculantQ3.star : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- **Sharpness.** `D* ∪ {3p²}` has energy exactly `242 p² - 356 p + 154`. -/
theorem roldan_q3_sharp (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    energy (icgAdj (27 * p ^ 2) (insert (3 * p ^ 2) (Dstar p))) (icgAdj_isHermitian _ _) =
      242 * (p : ℝ) ^ 2 - 356 * p + 154 := by
  have hp3 : p ≠ 3 := by omega
  have hND : 27 * p ^ 2 ∉ insert (3 * p ^ 2) (Dstar p) := fun hmem =>
    lt_irrefl _ (Nat.mem_properDivisors.mp (DstarPlus_subset p hp hp5 hmem)).2
  rw [energy_icgAdj_eq_exactEnergy p hp hp3 _ hND, maskOf_DstarPlus hp hp3,
    exactEnergy_starPlus p (by exact_mod_cast hp5)]
  push_cast
  ring

/-- The gap of `roldan_q3_gap` is attained, by the admissible set `D* ∪ {3p²} ≠ D*`. -/
theorem roldan_q3_gap_attained (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    insert (3 * p ^ 2) (Dstar p) ⊆ (27 * p ^ 2).properDivisors ∧
      insert (3 * p ^ 2) (Dstar p) ≠ Dstar p ∧
      energy (icgAdj (27 * p ^ 2) (insert (3 * p ^ 2) (Dstar p))) (icgAdj_isHermitian _ _) +
          24 * ((p : ℝ) ^ 2 - 2 * p + 2) =
        energy (icgAdj (27 * p ^ 2) (Dstar p)) (icgAdj_isHermitian _ _) := by
  refine ⟨DstarPlus_subset p hp hp5, DstarPlus_ne p hp hp5, ?_⟩
  rw [roldan_q3_sharp p hp hp5, energy_Dstar p hp hp5]
  ring

/-! ### The same for the mathlib `SimpleGraph.circulantGraph` model (`icgGraph`) -/

theorem energy_icgGraph_eq_icgAdj (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero (27 * p ^ 2)]
    (D : Finset ℕ) (hND : 27 * p ^ 2 ∉ D) :
    energy ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) (SimpleGraph.isHermitian_adjMatrix ℝ _) =
      energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) := by
  rw [energy_icgGraph_eq p hp hp3 D hND, energy_icgAdj_eq p hp hp3 D hND]

theorem roldan_q3_gap_graph (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (27 * p ^ 2)]
    (D : Finset ℕ) (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) (SimpleGraph.isHermitian_adjMatrix ℝ _) +
        24 * ((p : ℝ) ^ 2 - 2 * p + 2) ≤
      energy ((icgGraph (27 * p ^ 2) (Dstar p)).adjMatrix ℝ)
        (SimpleGraph.isHermitian_adjMatrix ℝ _) := by
  have hp3 : p ≠ 3 := by omega
  have hNot : ∀ E : Finset ℕ, E ⊆ (27 * p ^ 2).properDivisors → 27 * p ^ 2 ∉ E :=
    fun E hE hmem => lt_irrefl _ (Nat.mem_properDivisors.mp (hE hmem)).2
  rw [energy_icgGraph_eq_icgAdj p hp hp3 D (hNot D hD),
    energy_icgGraph_eq_icgAdj p hp hp3 (Dstar p) (hNot _ (Dstar_subset p hp5))]
  exact roldan_q3_gap p hp hp5 D hD hne

theorem roldan_q3_sharp_graph (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (27 * p ^ 2)] :
    energy ((icgGraph (27 * p ^ 2) (insert (3 * p ^ 2) (Dstar p))).adjMatrix ℝ)
        (SimpleGraph.isHermitian_adjMatrix ℝ _) =
      242 * (p : ℝ) ^ 2 - 356 * p + 154 := by
  have hp3 : p ≠ 3 := by omega
  rw [energy_icgGraph_eq_icgAdj p hp hp3 _
    (fun hmem => lt_irrefl _ (Nat.mem_properDivisors.mp (DstarPlus_subset p hp hp5 hmem)).2)]
  exact roldan_q3_sharp p hp hp5

end ICGBridge

#print axioms ICGBridge.roldan_q3_gap
#print axioms ICGBridge.roldan_q3_sharp
#print axioms ICGBridge.roldan_q3_gap_attained
#print axioms ICGBridge.roldan_q3_gap_graph
#print axioms ICGBridge.roldan_q3_sharp_graph
