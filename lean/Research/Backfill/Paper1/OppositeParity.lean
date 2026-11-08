import Research.Backfill.Paper1.GraphBridge
import Research.Backfill.Paper1.ClosedForms
import Research.ICGGeneralSwap

/-!
Proof source for full frozen Theorem1, Theorem2 and SummaryOppositeParity.
Real simple-graph energy, closed forms, admissibility and equality iff are all
included. Compilation and acceptance evidence is recorded separately by
check_oppositeparity.py; the source alone is not an acceptance receipt.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral

namespace OppositeParity

lemma energy_eq_matrix_of_subset {n : ℕ} {D : Finset ℕ}
    (hD : D ⊆ n.properDivisors) :
    Challenge.energy n D = ICGBridge.energy (ICGBridge.icgAdj n D)
      (ICGBridge.icgAdj_isHermitian n D) := by
  apply GraphBridge.graph_energy_eq
  intro hn
  exact Nat.self_notMem_properDivisors (hD hn)

lemma evenSet_admissible {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hab : Odd (a + b)) :
    Challenge.IsConnSet (p ^ a * q ^ b) (Challenge.evenSet p q a b) := by
  change (DstarPQ p q a b).Nonempty ∧ _
  refine ⟨⟨1, ?_⟩, DstarPQ_subset hp hq hpq hab⟩
  rw [mem_DstarPQ_iff]
  exact ⟨0, Nat.zero_le _, 0, Nat.zero_le _, ⟨0, rfl⟩, by simp⟩

lemma evenSet_value {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hab : Odd (a + b)) :
    Challenge.energy (p ^ a * q ^ b) (Challenge.evenSet p q a b) =
      (((p ^ a * q ^ b : ℕ) : ℝ) + Challenge.dClosed a p * Challenge.dClosed b q) / 2 := by
  rw [energy_eq_matrix_of_subset (evenSet_admissible hp hq hpq hab).2]
  have hpR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have he := energy_DstarPQ hp hq hpq hp3 hq3 a b
  rw [← Additional.dNorm_eq_L1, ← Additional.dNorm_eq_L1,
    ClosedForms.dNorm_eq_dClosed hpR, ClosedForms.dNorm_eq_dClosed hqR] at he
  change ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (DstarPQ p q a b))
    (ICGBridge.icgAdj_isHermitian _ _) = _
  push_cast
  linarith

/-- The full maximum statement, with its unique nonempty admissible maximizer. -/
lemma maximum {p q a b : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    (hab : Odd (a + b)) :
    Challenge.MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + Challenge.dClosed a p * Challenge.dClosed b q) / 2)
      {Challenge.evenSet p q a b} := by
  rcases hpq with ⟨hp, hq, hne, hpo, hqo⟩
  have hp3 := hp.odd_iff.mp hpo
  have hq3 := hq.odd_iff.mp hqo
  have hs := evenSet_admissible hp hq hne hab
  have hv := evenSet_value hp hq hne hp3 hq3 hab
  constructor
  · intro D hD
    have heq : D = Challenge.evenSet p q a b := Set.mem_singleton_iff.mp hD
    simpa [heq] using hs
  · intro D hD
    by_cases heq : D = Challenge.evenSet p q a b
    · subst D
      exact ⟨hv.le, iff_of_true hv (Set.mem_singleton _)⟩
    · have hlt := checkerboard_unique_max_odd p q a b hp hq hne
        (by omega) (by omega) hab D hD.2 heq
      change ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) D)
          (ICGBridge.icgAdj_isHermitian _ _) <
        ICGBridge.energy (ICGBridge.icgAdj (p ^ a * q ^ b) (Challenge.evenSet p q a b))
          (ICGBridge.icgAdj_isHermitian _ _) at hlt
      rw [← energy_eq_matrix_of_subset hD.2,
        ← energy_eq_matrix_of_subset hs.2, hv] at hlt
      refine ⟨hlt.le, ?_⟩
      exact iff_of_false (ne_of_lt hlt) (fun h => heq (Set.mem_singleton_iff.mp h))

end OppositeParity

theorem check_Theorem1 : Challenge.Theorem1 := by
  intro p q r s hpq _hq _hr
  exact OppositeParity.maximum hpq ⟨r + s, by ring⟩

theorem check_Theorem2 : Challenge.Theorem2 := by
  intro p r s hp hp5 _hr
  have hpq : Challenge.DistinctOddPrimes p 3 :=
    ⟨hp, Nat.prime_three, by omega, hp.odd_of_ne_two (by omega), by decide⟩
  exact OppositeParity.maximum hpq ⟨r + s, by ring⟩

theorem check_SummaryOppositeParity : Challenge.SummaryOppositeParity := by
  intro p q a b hpq _ha _hb hab
  exact OppositeParity.maximum hpq hab

#print axioms check_Theorem1
#print axioms check_Theorem2
#print axioms check_SummaryOppositeParity
end CodexPaper1
