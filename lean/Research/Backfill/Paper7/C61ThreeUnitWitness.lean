import Research.Backfill.Paper7.C61RootThreeReduction

/-! NEW SOURCE ONLY. No execution, enumeration, or acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge Paper7C61Profile Paper7Lemma22Gaps
open scoped BigOperators Classical

def FullUnitWitness (p q : Fin 6 → ℕ) : Prop :=
  ∀ k, 0 < q k → ∃ y : Fin 6 → ℝ,
    y k = 0 ∧ y (nxt 6 k) = 1 ∧
    ∀ j, (0 < q j → y j = 0) ∧
      (q j = 0 → y (prv 6 j) + y (nxt 6 j) = (1 - (p j : ℝ)) * y j)
#print axioms Paper7C61Three.FullUnitWitness

theorem beta_six_full_unit_witness (p q : Fin 6 → ℕ)
    (hb : unitExponent p q = 6) : FullUnitWitness p q := by
  intro k hk
  have hkm : k ∈ Kq 6 q := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
  have hK : (Kq 6 q).Nonempty := ⟨k, hkm⟩
  have hc : (Kq 6 q).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kq 6 q))
  have hd : deltaE 6 p q 1 = (Kq 6 q).card := by
    unfold unitExponent at hb
    omega
  have hdim : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (Wmat 6 p q 1))) =
      Module.finrank ℝ ({j : Fin 6 // j ∈ Kq 6 q} → ℝ) := by
    simpa only [deltaE, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hd
  have hsur : Function.Surjective (supportSuccessorMap 6 p q 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (supportSuccessorMap_injective 6 p q 1 hK)
  obtain ⟨y, hy⟩ := hsur (fun _ => 1)
  refine ⟨y.1, kernel_zero_on_support 6 p q 1 y.1 y.property k hkm, ?_, ?_⟩
  · exact congrFun hy ⟨k, hkm⟩
  · intro j
    constructor
    · intro hj
      exact kernel_zero_on_support 6 p q 1 y.1 y.property j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
    · intro hj
      have hnot : j ∉ Kq 6 q := by simp [Kq, hj]
      simpa only [one_mul] using
        kernel_recurrence_off_support 6 p q 1 y.1 y.property j hnot
#print axioms Paper7C61Three.beta_six_full_unit_witness

theorem nxt_six (k : Fin 6) : nxt 6 k = k + 1 := by
  exact finRotate_apply k
#print axioms Paper7C61Three.nxt_six

theorem prv_six (k : Fin 6) : prv 6 k = k + 5 := by
  fin_cases k <;> decide
#print axioms Paper7C61Three.prv_six

def shiftSix {α : Type} (f : Fin 6 → α) : Fin 6 → α := fun k => f (k + 1)
#print axioms Paper7C61Three.shiftSix

theorem full_unit_witness_shift (p q : Fin 6 → ℕ)
    (h : FullUnitWitness p q) : FullUnitWitness (shiftSix p) (shiftSix q) := by
  intro k hk
  obtain ⟨y, hy0, hy1, hy⟩ := h (k + 1) hk
  refine ⟨shiftSix y, hy0, ?_, ?_⟩
  · simpa only [shiftSix, nxt_six, add_assoc] using hy1
  · intro j
    constructor
    · exact (hy (j + 1)).1
    · intro hj
      have hj' := (hy (j + 1)).2 hj
      simpa only [shiftSix, prv_six, nxt_six, add_assoc, add_comm, add_left_comm] using hj'
#print axioms Paper7C61Three.full_unit_witness_shift

theorem full_unit_witness_adjacent (p q : Fin 6 → ℕ)
    (h : FullUnitWitness p q) (k : Fin 6) (hk : 0 < q k) : q (nxt 6 k) = 0 := by
  obtain ⟨y, _, hy1, hy⟩ := h k hk
  by_contra hn
  have hz := (hy (nxt 6 k)).1 (Nat.pos_of_ne_zero hn)
  linarith
#print axioms Paper7C61Three.full_unit_witness_adjacent

end Paper7C61Three
