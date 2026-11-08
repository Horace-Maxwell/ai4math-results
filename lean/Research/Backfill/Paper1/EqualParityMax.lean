import Research.Backfill.Paper1.OppositeParity
import Research.ICGEqualParityUnique
import Research.ICGEqualParityBGraph

/-!
Proof source for two exact frozen goals. Compilation and acceptance evidence
are recorded separately; this source header makes no acceptance claim.

Full frozen Paper 1 Theorem3 and Theorem4, including both orientations,
nonempty proper-divisor candidates, upper bounds and equality iff.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.

Existing corollaryA/corollaryB provide the old matrix-energy statements.
The proof below supplies the actual simple-graph bridge, closed forms and
nonemptiness. It does not replace any frozen goal by a conditional interface.
-/

set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral

namespace EqualParityMax

lemma L1_eq_dClosed {x : ℝ} (hx : 2 < x) (k : ℕ) :
    ICGGeneral.L1 x k ICGGeneral.sgnv = Challenge.dClosed k x := by
  rw [← Additional.dNorm_eq_L1]
  exact ClosedForms.dNorm_eq_dClosed hx k

lemma Tv_last_eq_deltaK {x : ℝ} (hx : 2 < x) (k : ℕ) :
    ICGGeneral.Tv x k ICGGeneral.sgnv k = Challenge.deltaK k x := by
  have h := ClosedForms.last_alt_eq_deltaK hx k
  rw [Additional.tMulVec_eq_Tv x k Challenge.sAlt k le_rfl] at h
  exact h

lemma oddSet_nonempty (p q a b : ℕ) (ha : 1 ≤ a) :
    (Challenge.oddSet p q a b).Nonempty := by
  change (ICGEqualParity.DantiPQ p q a b).Nonempty
  refine ⟨p, ICGEqualParity.mem_DantiPQ_iff.mpr ?_⟩
  exact ⟨1, ha, 0, Nat.zero_le _, by decide, by simp⟩

lemma pow_product_ne_one {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 1 ≤ a) :
    p ^ a * q ^ b ≠ 1 := by
  intro h
  have hzero : a = 0 ∧ b = 0 := (pq_inj hp hq hpq).mp (by simpa using h)
  omega

lemma evenSet_erase_nonempty {p q a b : ℕ} (hn : p ^ a * q ^ b ≠ 1) :
    ((Challenge.evenSet p q a b).erase (p ^ a * q ^ b)).Nonempty := by
  refine ⟨1, Finset.mem_erase.mpr ⟨Ne.symm hn, ?_⟩⟩
  change 1 ∈ DstarPQ p q a b
  rw [mem_DstarPQ_iff]
  exact ⟨0, Nat.zero_le _, 0, Nat.zero_le _, ⟨0, rfl⟩, by simp⟩

/-- Convert the full old two-maximizer result into frozen MaxEnergy.
Both candidates are supplied with nonemptiness; both reverse equality cases
use their actual energies. -/
lemma maximum_of_matrix {n : ℕ} {A B : Finset ℕ} {V : ℝ}
    (hA : Challenge.IsConnSet n A) (hB : Challenge.IsConnSet n B)
    (hv : ICGBridge.energy (ICGBridge.icgAdj n A)
      (ICGBridge.icgAdj_isHermitian n A) = V)
    (hBA : ICGBridge.energy (ICGBridge.icgAdj n B)
      (ICGBridge.icgAdj_isHermitian n B) =
      ICGBridge.energy (ICGBridge.icgAdj n A) (ICGBridge.icgAdj_isHermitian n A))
    (hmax : ∀ D : Finset ℕ, D ⊆ n.properDivisors →
      ICGBridge.energy (ICGBridge.icgAdj n D) (ICGBridge.icgAdj_isHermitian n D) ≤
        ICGBridge.energy (ICGBridge.icgAdj n A) (ICGBridge.icgAdj_isHermitian n A) ∧
      (ICGBridge.energy (ICGBridge.icgAdj n D) (ICGBridge.icgAdj_isHermitian n D) =
        ICGBridge.energy (ICGBridge.icgAdj n A) (ICGBridge.icgAdj_isHermitian n A) →
        D = A ∨ D = B)) :
    Challenge.MaxEnergy n V {A, B} := by
  have hAg : Challenge.energy n A = V := by
    rw [OppositeParity.energy_eq_matrix_of_subset hA.2]
    exact hv
  have hBg : Challenge.energy n B = V := by
    rw [OppositeParity.energy_eq_matrix_of_subset hB.2, hBA, hv]
  constructor
  · intro D hD
    have hmem : D = A ∨ D = B := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hD
    rcases hmem with rfl | rfl
    · exact hA
    · exact hB
  · intro D hD
    obtain ⟨hle, himp⟩ := hmax D hD.2
    rw [← OppositeParity.energy_eq_matrix_of_subset hD.2, hv] at hle himp
    refine ⟨hle, ?_⟩
    constructor
    · intro h
      have hmem := himp h
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    · intro h
      have hmem : D = A ∨ D = B := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
      rcases hmem with rfl | rfl
      · exact hAg
      · exact hBg

lemma maximum_one {p q m : ℕ} (hpq : Challenge.DistinctOddPrimes p q) (hm : Odd m) :
    Challenge.MaxEnergy (p ^ 1 * q ^ m)
      (((((p ^ 1 * q ^ m : ℕ) : ℝ)) + (3 * (p : ℝ) - 4) * Challenge.dClosed m q) / 2 -
        ((p : ℝ) - 2) * Challenge.deltaK m q)
      {Challenge.oddSet p q 1 m,
        (Challenge.evenSet p q 1 m).erase (p ^ 1 * q ^ m)} := by
  rcases hpq with ⟨hp, hq, hne, hpo, hqo⟩
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpo
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqo
  have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  obtain ⟨hAsub, hBsub, hval, hBA, hmax⟩ :=
    ICGEqualParity.corollaryA p q m hp hq hne hp3 hq3 hm
  have hA : Challenge.IsConnSet (p ^ 1 * q ^ m) (ICGEqualParity.DantiPQ p q 1 m) :=
    ⟨oddSet_nonempty p q 1 m le_rfl, hAsub⟩
  have hB : Challenge.IsConnSet (p ^ 1 * q ^ m) (ICGEqualParity.DtruncPQ p q m) :=
    ⟨evenSet_erase_nonempty (pow_product_ne_one hp hq hne le_rfl), hBsub⟩
  have hv : ICGBridge.energy
      (ICGBridge.icgAdj (p ^ 1 * q ^ m) (ICGEqualParity.DantiPQ p q 1 m))
      (ICGBridge.icgAdj_isHermitian _ _) =
      (((((p ^ 1 * q ^ m : ℕ) : ℝ)) + (3 * (p : ℝ) - 4) * Challenge.dClosed m q) / 2 -
        ((p : ℝ) - 2) * Challenge.deltaK m q) := by
    rw [L1_eq_dClosed hqR, Tv_last_eq_deltaK hqR] at hval
    push_cast
    simp only [pow_one]
    linarith
  exact maximum_of_matrix hA hB hv hBA hmax

lemma maximum_two {p q b : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    (hb : Even b) (hb2 : 2 ≤ b) :
    Challenge.MaxEnergy (p ^ 2 * q ^ b)
      (((((p ^ 2 * q ^ b : ℕ) : ℝ)) +
          (5 * (p : ℝ) ^ 2 - 8 * p + 4) * Challenge.dClosed b q) / 2 -
        ((p : ℝ) ^ 2 - 2 * p + 2) * Challenge.deltaK b q)
      {Challenge.oddSet p q 2 b,
        (Challenge.evenSet p q 2 b).erase (p ^ 2 * q ^ b)} := by
  rcases hpq with ⟨hp, hq, hne, hpo, hqo⟩
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpo
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqo
  have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  obtain ⟨hAsub, hBsub, hval, hBA, hmax⟩ :=
    ICGEqualParityB.corollaryB p q b hp hq hne hp3 hq3 hb hb2
  have hA : Challenge.IsConnSet (p ^ 2 * q ^ b) (ICGEqualParity.DantiPQ p q 2 b) :=
    ⟨oddSet_nonempty p q 2 b (by decide), hAsub⟩
  have hB : Challenge.IsConnSet (p ^ 2 * q ^ b) (ICGEqualParityB.DtruncB p q b) :=
    ⟨evenSet_erase_nonempty (pow_product_ne_one hp hq hne (by decide)), hBsub⟩
  have hv : ICGBridge.energy
      (ICGBridge.icgAdj (p ^ 2 * q ^ b) (ICGEqualParity.DantiPQ p q 2 b))
      (ICGBridge.icgAdj_isHermitian _ _) =
      (((((p ^ 2 * q ^ b : ℕ) : ℝ)) +
          (5 * (p : ℝ) ^ 2 - 8 * p + 4) * Challenge.dClosed b q) / 2 -
        ((p : ℝ) ^ 2 - 2 * p + 2) * Challenge.deltaK b q) := by
    rw [L1_eq_dClosed hqR, Tv_last_eq_deltaK hqR] at hval
    push_cast
    linarith
  exact maximum_of_matrix hA hB hv hBA hmax

lemma oddSet_swap (p q a b : ℕ) :
    Challenge.oddSet q p a b = Challenge.oddSet p q b a :=
  ICGEqualParityB.DantiPQ_swap p q a b

lemma evenSet_swap (p q a b : ℕ) :
    Challenge.evenSet q p a b = Challenge.evenSet p q b a :=
  ICGEqualParityB.DstarPQ_swap p q a b

lemma distinctOddPrimes_swap {p q : ℕ} (h : Challenge.DistinctOddPrimes p q) :
    Challenge.DistinctOddPrimes q p :=
  ⟨h.2.1, h.1, Ne.symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

end EqualParityMax

/-- Both orientations, including the minimal odd exponent m = 1. -/
theorem check_Theorem3 : Challenge.Theorem3 := by
  intro p q m hpq _hm1 hm
  constructor
  · simpa only [pow_one] using EqualParityMax.maximum_one hpq hm
  · have h := EqualParityMax.maximum_one (EqualParityMax.distinctOddPrimes_swap hpq) hm
    rw [EqualParityMax.oddSet_swap, EqualParityMax.evenSet_swap] at h
    simpa only [pow_one, mul_comm] using h

/-- Both orientations, including the smallest even exponent b = 2. -/
theorem check_Theorem4 : Challenge.Theorem4 := by
  intro p q b hpq hb2 hb
  constructor
  · exact EqualParityMax.maximum_two hpq hb hb2
  · have h := EqualParityMax.maximum_two (EqualParityMax.distinctOddPrimes_swap hpq) hb hb2
    rw [EqualParityMax.oddSet_swap, EqualParityMax.evenSet_swap] at h
    simpa only [mul_comm] using h

#print axioms check_Theorem3
#print axioms check_Theorem4
end CodexPaper1
