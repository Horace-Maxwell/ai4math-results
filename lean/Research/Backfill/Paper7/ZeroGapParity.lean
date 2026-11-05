import Research.Backfill.Paper7.MainCycleQzeroReduction

/-! Source-only parity propagation from equality in the actual zero-gap
count. It uses induction along a cycle, not a support table. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge
open scoped Classical

theorem saturated_zero_gap (b : ℕ) (p : Fin b → ℕ)
    (hdelta : delta0 b p = (Kp b p).card) (k : Fin b) (hk : 0 < p k) :
    ∃ d ∈ Finset.Icc 1 b, Even d ∧ ((finRotate b)^d) k ∈ Kp b p ∧
      ∀ d' ∈ Finset.Ico 1 d, ((finRotate b)^d') k ∉ Kp b p := by
  have hkK : k ∈ Kp b p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
  have hK : Kp b p ≠ ∅ := by intro hh; rw [hh] at hkK; exact Finset.notMem_empty k hkK
  rw [delta0,ite_eq_right hK] at hdelta
  unfold evenGaps at hdelta
  exact Finset.card_filter_eq_iff.mp hdelta k hkK
#print axioms Paper7MainReduction.saturated_zero_gap

theorem saturated_zero_gap_odd_rotation (b : ℕ) (p : Fin b → ℕ)
    (hdelta : delta0 b p = (Kp b p).card) :
    ∀ (d : ℕ) (k : Fin b), 0 < p k → Odd d → d < b → p (((finRotate b)^d) k) = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk hd hdb
    obtain ⟨e,he,heven,hend,hclear⟩ := saturated_zero_gap b p hdelta k hk
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hd1 : 1 ≤ d := by obtain ⟨r,hr⟩ := hd; omega
    by_cases hde : d < e
    · have hz := hclear d (Finset.mem_Ico.mpr ⟨hd1,hde⟩)
      have hh : ¬ 0 < p (((finRotate b)^d) k) := by
        simpa only [Kp,Finset.mem_filter,Finset.mem_univ,true_and] using hz
      omega
    · have hed : e < d := by
        obtain ⟨r,hr⟩ := hd
        obtain ⟨s,hs⟩ := heven
        omega
      have hodd : Odd (d-e) := by
        obtain ⟨r,hr⟩ := hd
        obtain ⟨s,hs⟩ := heven
        exact ⟨r-s,by omega⟩
      have hpos : 0 < p (((finRotate b)^e) k) := (Finset.mem_filter.mp hend).2
      have hz := ih (d-e) (by omega) (((finRotate b)^e) k) hpos hodd (by omega)
      have hrot : ((finRotate b)^(d-e)) (((finRotate b)^e) k) = ((finRotate b)^d) k := by
        change ((finRotate b)^(d-e)*(finRotate b)^e) k = _
        rw [← pow_add,Nat.sub_add_cancel (by omega : e ≤ d)]
      rw [hrot] at hz
      exact hz
#print axioms Paper7MainReduction.saturated_zero_gap_odd_rotation

theorem twelve_saturated_rotated_odd_zero (p : Fin 12 → ℕ)
    (hdelta : delta0 12 p = (Kp 12 p).card) (k : Fin 12) (hk : 0 < p k) :
    p (1+k) = 0 ∧ p (3+k) = 0 ∧ p (5+k) = 0 ∧
      p (7+k) = 0 ∧ p (9+k) = 0 ∧ p (11+k) = 0 := by
  have hr (d : Fin 12) : ((finRotate 12)^d.val) k = d+k := by
    fin_cases d <;> fin_cases k <;> decide
  have hz (d : Fin 12) (hd : Odd d.val) : p (d+k) = 0 := by
    rw [← hr d]
    exact saturated_zero_gap_odd_rotation 12 p hdelta d.val k hk hd d.isLt
  exact ⟨hz 1 (by decide),hz 3 (by decide),hz 5 (by decide),
    hz 7 (by decide),hz 9 (by decide),hz 11 (by decide)⟩
#print axioms Paper7MainReduction.twelve_saturated_rotated_odd_zero

end Paper7MainReduction
