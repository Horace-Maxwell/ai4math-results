import Research.Backfill.Paper1.GeneralEqG
import Research.Backfill.Paper1.OddSet

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.GraphTransport
open Finset BackfillPaper1.Challenge ICGGeneral

/-- The actual sign matrix of a divisor set. -/
def signs (p q : ℕ) (D : Finset ℕ) (i j : ℕ) : ℝ := 2 * divMat p q D i j - 1

lemma signs_isSign (p q a b : ℕ) (D : Finset ℕ) : IsSignMat a b (signs p q D) := by
  intro i _hi j _hj
  unfold signs divMat
  split_ifs <;> norm_num

lemma signs_injective {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    {D E : Finset ℕ} (hD : D ⊆ (p ^ a * q ^ b).properDivisors)
    (hE : E ⊆ (p ^ a * q ^ b).properDivisors)
    (he : MatEq a b (signs p q D) (signs p q E)) : D = E := by
  have hmem : ∀ i ≤ a, ∀ j ≤ b, p ^ i * q ^ j ∈ D ↔ p ^ i * q ^ j ∈ E := by
    intro i hi j hj
    have hh := he i hi j hj
    unfold signs divMat at hh
    split_ifs at hh <;> norm_num at hh <;> simp_all
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, j, hj, rfl⟩ := pq_dvd_rep hp hq (Nat.mem_properDivisors.mp (hD hx)).1
    exact (hmem i hi j hj).mp hx
  · intro hx
    obtain ⟨i, hi, j, hj, rfl⟩ := pq_dvd_rep hp hq (Nat.mem_properDivisors.mp (hE hx)).1
    exact (hmem i hi j hj).mpr hx

lemma truncated_subset {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (evenSet p q a b).erase (p ^ a * q ^ b) ⊆ (p ^ a * q ^ b).properDivisors := by
  intro x hx
  obtain ⟨hxn, hxs⟩ := mem_erase.mp hx
  obtain ⟨i, hi, j, hj, _hev, rfl⟩ := mem_DstarPQ_iff.mp hxs
  rw [Nat.mem_properDivisors]
  have hd : p ^ i * q ^ j ∣ p ^ a * q ^ b := (pq_dvd_iff hp hq hne).mpr ⟨hi, hj⟩
  have hpos : 0 < p ^ a * q ^ b := by have := hp.pos; have := hq.pos; positivity
  exact ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd hpos hd) hxn⟩

lemma odd_signs {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    MatEq a b (signs p q (oddSet p q a b)) Yminus :=
  CodexPaper1.OddSet.odd_sign hp hq hne

lemma plus_eq {a b : ℕ} (hab : Even (a + b)) (i j : ℕ) :
    Yplus a b i j = if Even (i + j) ∧ ¬ (i = a ∧ j = b) then 1 else -1 := by
  unfold Yplus sAlt
  by_cases hc : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hc
    rw [ite_eq_left ⟨rfl, rfl⟩, ← pow_add, hab.neg_one_pow,
      ite_eq_right (fun h => h.2 ⟨rfl, rfl⟩)]
    norm_num
  · rw [ite_eq_right hc, sub_zero, ← pow_add]
    by_cases he : Even (i + j)
    · rw [he.neg_one_pow, ite_eq_left ⟨he, hc⟩]
    · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow, ite_eq_right (fun h => he h.1)]

lemma truncated_signs {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hab : Even (a + b)) :
    MatEq a b (signs p q ((evenSet p q a b).erase (p ^ a * q ^ b))) (Yplus a b) := by
  intro i hi j hj
  have hm : p ^ i * q ^ j ∈ (evenSet p q a b).erase (p ^ a * q ^ b) ↔
      Even (i + j) ∧ ¬ (i = a ∧ j = b) := by
    change p ^ i * q ^ j ∈ (DstarPQ p q a b).erase (p ^ a * q ^ b) ↔ _
    rw [mem_erase, pq_mem_DstarPQ hp hq hne hi hj]
    constructor
    · rintro ⟨hn, he⟩; exact ⟨he, fun h => hn (by rw [h.1, h.2])⟩
    · rintro ⟨he, hn⟩; exact ⟨fun h => hn ((pq_inj hp hq hne).mp h), he⟩
  unfold signs divMat
  rw [plus_eq hab]
  by_cases h : Even (i + j) ∧ ¬ (i = a ∧ j = b)
  · rw [ite_eq_left (hm.mpr h), ite_eq_left h]; norm_num
  · rw [ite_eq_right (fun hh => h (hm.mp hh)), ite_eq_right h]; norm_num

lemma graph_result {p q a b : ℕ} (hpq : DistinctOddPrimes p q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : Even (a + b)) (hs : SignConclusion a p q) :
    MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 - deltaK a p * deltaK b q)
      {oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)} := by
  classical
  have hp := hpq.1
  have hq := hpq.2.1
  have hne := hpq.2.2.1
  have hpR : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by have := hp.odd_iff.mp hpq.2.2.2.1; omega)
  have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by have := hq.odd_iff.mp hpq.2.2.2.2; omega)
  have hA : IsConnSet (p ^ a * q ^ b) (oddSet p q a b) :=
    ⟨CodexPaper1.EqualParityMax.oddSet_nonempty p q a b ha,
      ICGEqualParity.DantiPQ_subset hp hq hne hab⟩
  have hB : IsConnSet (p ^ a * q ^ b) ((evenSet p q a b).erase (p ^ a * q ^ b)) :=
    ⟨CodexPaper1.EqualParityMax.evenSet_erase_nonempty
      (CodexPaper1.EqualParityMax.pow_product_ne_one hp hq hne ha), truncated_subset hp hq hne⟩
  constructor
  · intro D hD
    rcases Set.mem_insert_iff.mp hD with h | h
    · simpa only [h] using hA
    · have he := Set.mem_singleton_iff.mp h
      simpa only [he] using hB
  · intro D hD
    have hcorner : signs p q D a b = -1 := by
      unfold signs divMat
      rw [ite_eq_right (fun h => Nat.self_notMem_properDivisors (hD.2 h))]
      norm_num
    have hpar : b % 2 = a % 2 := by have hh := Nat.even_iff.mp hab; omega
    obtain ⟨hle, hiff⟩ := hs b hb hpar (signs p q D) (signs_isSign p q a b D) hcorner
    have henergy := CodexPaper1.check_GeneralEqG p q a b hp hq hne ha hb D hD.2
    change 2 * energy (p ^ a * q ^ b) D = (p ^ a * q ^ b : ℕ) + Gval a b p q (signs p q D) at henergy
    unfold Theta at hle hiff
    rw [CodexPaper1.ClosedForms.dNorm_eq_dClosed hpR,
      CodexPaper1.ClosedForms.dNorm_eq_dClosed hqR] at hle hiff
    have hm : (MatEq a b (signs p q D) Yminus ∨ MatEq a b (signs p q D) (Yplus a b)) ↔
        D ∈ ({oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)} : Set (Finset ℕ)) := by
      constructor
      · rintro (hh | hh)
        · left
          exact signs_injective hp hq hD.2 hA.2 (fun i hi j hj => (hh i hi j hj).trans (odd_signs hp hq hne i hi j hj).symm)
        · right
          apply Set.mem_singleton_iff.mpr
          exact signs_injective hp hq hD.2 hB.2 (fun i hi j hj => (hh i hi j hj).trans (truncated_signs hp hq hne hab i hi j hj).symm)
      · intro hh
        rcases Set.mem_insert_iff.mp hh with hh | hh
        · subst D; exact Or.inl (odd_signs hp hq hne)
        · have he := Set.mem_singleton_iff.mp hh
          subst D; exact Or.inr (truncated_signs hp hq hne hab)
    refine ⟨by linarith, ?_⟩
    rw [← hm, ← hiff]
    constructor <;> intro hh <;> linarith

end CodexPaper1.TaskE.GraphTransport
#print axioms CodexPaper1.TaskE.GraphTransport.graph_result
