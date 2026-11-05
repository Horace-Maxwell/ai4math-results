import Research.Backfill.Paper7.MomentB6DominantWeights
import Research.Backfill.Paper7.MomentB6SevenWeights

/-! Source-only endpoint fibre bridges, generic in the number of coordinates.
The original Q=0/1 boundary and complement Q=total-1 are all counted through
actual bounded assignments. No proposed numerical slice value is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

theorem boundedQDP_zero_capacity_eq_one (n : ℕ) (z : Fin n → ℕ) :
    Paper7MomentDP.boundedQDP n z 0 = 1 := by
  rw [boundedQDP_complement n z 0 (Nat.zero_le _),Nat.sub_zero]
  exact boundedQDP_full_capacity_eq_one n z
#print axioms Paper7MomentCounts.boundedQDP_zero_capacity_eq_one

def boundedQSingletonAssignment (n : ℕ) (z : Fin n → ℕ)
    (i : {i : Fin n // 0 < z i}) : (k : Fin n) → Fin (z k + 1) := fun k =>
  ⟨if k = i.val then 1 else 0,by
    by_cases hk : k = i.val
    · subst k
      have hi := i.property
      simp only [↓reduceIte]
      omega
    · simp [hk]⟩
#print axioms Paper7MomentCounts.boundedQSingletonAssignment

def boundedQSingletonFibreMap (n : ℕ) (z : Fin n → ℕ) :
    {i : Fin n // 0 < z i} → {q : (k : Fin n) → Fin (z k + 1) // ∑ k, (q k).val = 1} :=
  fun i => ⟨boundedQSingletonAssignment n z i,by simp [boundedQSingletonAssignment]⟩
#print axioms Paper7MomentCounts.boundedQSingletonFibreMap

theorem boundedQSingletonFibreMap_bijective (n : ℕ) (z : Fin n → ℕ) :
    Function.Bijective (boundedQSingletonFibreMap n z) := by
  constructor
  · intro i j he
    apply Subtype.ext
    have hv := congrArg (fun q => (q.val i.val).val) he
    change (if i.val = i.val then 1 else 0) = (if i.val = j.val then 1 else 0) at hv
    by_contra hn
    simp [hn] at hv
  · intro q
    have hex : ∃ i, (q.val i).val ≠ 0 := by
      by_contra hn
      have hz : ∀ i, (q.val i).val = 0 := by
        intro i
        by_contra hi
        exact hn ⟨i,hi⟩
      have hs : (∑ i, (q.val i).val) = 0 := Finset.sum_eq_zero (fun i _ => hz i)
      have hq := q.property
      omega
    obtain ⟨i,hi⟩ := hex
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun k => (q.val k).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hqi : (q.val i).val = 1 := by have hq := q.property; omega
    have hipos : 0 < z i := by have hb := (q.val i).isLt; omega
    refine ⟨⟨i,hipos⟩,?_⟩
    apply Subtype.ext
    funext k
    apply Fin.ext
    by_cases hki : k = i
    · subst k
      simp [boundedQSingletonFibreMap,boundedQSingletonAssignment,hqi]
    · have he := Finset.sum_erase_add Finset.univ (fun j => (q.val j).val) (Finset.mem_univ i)
      have hk : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩
      have hb := Finset.single_le_sum (s := Finset.univ.erase i) (f := fun j => (q.val j).val)
        (fun _ _ => Nat.zero_le _) hk
      have hz : (q.val k).val = 0 := by have hq := q.property; omega
      simp [boundedQSingletonFibreMap,boundedQSingletonAssignment,hki,hz]
#print axioms Paper7MomentCounts.boundedQSingletonFibreMap_bijective

theorem boundedQDP_one_eq_positive_support_card (n : ℕ) (z : Fin n → ℕ) :
    Paper7MomentDP.boundedQDP n z 1 = Nat.card {i : Fin n // 0 < z i} := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  exact Nat.card_congr (Equiv.ofBijective (boundedQSingletonFibreMap n z)
    (boundedQSingletonFibreMap_bijective n z)).symm
#print axioms Paper7MomentCounts.boundedQDP_one_eq_positive_support_card

theorem boundedQDP_capacity_sub_one_eq_positive_support_card (n : ℕ) (z : Fin n → ℕ)
    (hpos : 0 < ∑ i, z i) :
    Paper7MomentDP.boundedQDP n z ((∑ i, z i) - 1) = Nat.card {i : Fin n // 0 < z i} := by
  have h := boundedQDP_complement n z 1 (by omega)
  rw [← h]
  exact boundedQDP_one_eq_positive_support_card n z
#print axioms Paper7MomentCounts.boundedQDP_capacity_sub_one_eq_positive_support_card

theorem b6_total_nine_endpoint_weights (z : Fin 6 → ℕ) (hZ : (∑ i, z i) = 9) :
    Paper7MomentDP.boundedQDP 6 z 0 = 1 ∧
      Paper7MomentDP.boundedQDP 6 z 8 = Nat.card {i : Fin 6 // 0 < z i} ∧
      Paper7MomentDP.boundedQDP 6 z 9 = 1 := by
  refine ⟨boundedQDP_zero_capacity_eq_one 6 z,?_,?_⟩
  · have h := boundedQDP_capacity_sub_one_eq_positive_support_card 6 z (by omega)
    simpa only [hZ] using h
  · have h := boundedQDP_full_capacity_eq_one 6 z
    simpa only [hZ] using h
#print axioms Paper7MomentCounts.b6_total_nine_endpoint_weights

end Paper7MomentCounts
