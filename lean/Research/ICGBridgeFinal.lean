import Research.CirculantQ3
import Research.ICGBridgeMain

/-!
# Roldán's Conjecture 1.3 (arXiv:2604.09491), case `q = 3`, for the genuine graph energy

Combines the spectral bridge (`Research/ICGBridge{Spectral,Ramanujan,Energy,Main}.lean`) with the
arithmetic core `CirculantQ3.exactEnergy_strict` (`Research/CirculantQ3.lean`).

Main statements:
* `ICGBridge.roldan_q3` : for every prime `p ≥ 5` and every `D ⊆ properDivisors (27 p²)` with
  `D ≠ D* = {1, p², 3p, 9, 9p², 27p}`,
  `energy (icgAdj (27 p²) D) < energy (icgAdj (27 p²) D*)`,
  where `icgAdj n D : Matrix (Fin n) (Fin n) ℝ` has entry `1` iff `gcd((j - i) mod n, n) ∈ D`
  and `energy A = ∑ i, |eigenvalue_i(A)|` (mathlib `Matrix.IsHermitian.eigenvalues`).
* `ICGBridge.roldan_q3_graph` : the same for the adjacency matrix of mathlib's
  `SimpleGraph.circulantGraph` on `ZMod (27 p²)` with jumps `{s | gcd(s, 27 p²) ∈ D}`.
* `ICGBridge.energy_Dstar` : `energy (icgAdj (27 p²) D*) = 266 p² - 404 p + 202`.
-/

namespace ICGBridge

/-- The verbatim copies used in `ICGBridgeMain` are definitionally the definitions of
`Research/CirculantQ3.lean`. -/
theorem copy_exactEnergy_eq : Copy.exactEnergy = CirculantQ3.exactEnergy := rfl

theorem copy_star_eq : Copy.star = CirculantQ3.star := rfl

theorem copy_chosen_eq : Copy.chosen = CirculantQ3.chosen := rfl

/-- The arithmetic core `CirculantQ3.exactEnergy_strict`, restated for the copies. -/
theorem copy_exactEnergy_strict (P : ℤ) (hP : 5 ≤ P) (mask : Fin 2048) (hm : mask ≠ Copy.star) :
    Copy.exactEnergy P mask < Copy.exactEnergy P Copy.star := by
  rw [copy_star_eq] at hm
  rw [copy_exactEnergy_eq, copy_star_eq]
  exact CirculantQ3.exactEnergy_strict P hP mask hm

/-- **Spectral bridge**, stated with the genuine `CirculantQ3.exactEnergy`. -/
theorem energy_icgAdj_eq_exactEnergy (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (D : Finset ℕ)
    (hND : 27 * p ^ 2 ∉ D) :
    energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) =
      ((CirculantQ3.exactEnergy p (maskOf p D) : ℤ) : ℝ) := by
  rw [← copy_exactEnergy_eq]
  exact energy_icgAdj_eq p hp hp3 D hND

/-- **Roldán's Conjecture 1.3 for `q = 3`** (adjacency-matrix form). -/
theorem roldan_q3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (D : Finset ℕ)
    (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) <
      energy (icgAdj (27 * p ^ 2) (Dstar p)) (icgAdj_isHermitian _ _) :=
  roldan_q3_of_arith copy_exactEnergy_strict p hp hp5 D hD hne

/-- **Roldán's Conjecture 1.3 for `q = 3`** (mathlib `SimpleGraph.circulantGraph` form). -/
theorem roldan_q3_graph (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (27 * p ^ 2)]
    (D : Finset ℕ) (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) (SimpleGraph.isHermitian_adjMatrix ℝ _) <
      energy ((icgGraph (27 * p ^ 2) (Dstar p)).adjMatrix ℝ)
        (SimpleGraph.isHermitian_adjMatrix ℝ _) :=
  roldan_q3_graph_of_arith copy_exactEnergy_strict p hp hp5 D hD hne

/-- The maximal energy (Theorem 1.2 of the paper at `q = 3`):
`E(ICG(27 p², D*)) = 266 p² - 404 p + 202`. -/
theorem energy_Dstar (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    energy (icgAdj (27 * p ^ 2) (Dstar p)) (icgAdj_isHermitian _ _) =
      266 * (p : ℝ) ^ 2 - 404 * p + 202 := by
  have hp3 : p ≠ 3 := by omega
  have hND : 27 * p ^ 2 ∉ Dstar p := by
    intro hmem
    have := Nat.mem_properDivisors.mp (Dstar_subset p hp5 hmem)
    exact lt_irrefl _ this.2
  rw [energy_icgAdj_eq_exactEnergy p hp hp3 (Dstar p) hND, maskOf_Dstar hp hp3, copy_star_eq,
    CirculantQ3.exactEnergy_star p (by exact_mod_cast hp5)]
  push_cast
  ring

end ICGBridge

#print axioms ICGBridge.roldan_q3
#print axioms ICGBridge.roldan_q3_graph
#print axioms ICGBridge.energy_Dstar
#print axioms ICGBridge.energy_icgAdj_eq_exactEnergy
