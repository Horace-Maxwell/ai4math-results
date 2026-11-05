import Research.Backfill.Paper7.C61ClearedProfile
import Research.Backfill.Paper7.C61OrbitHelpers

/-! Source-only candidate. The sole parameter hypothesis is the original
zero exponent being six. Every positive site then starts an even gap;
this forces all positive sites into one parity class of the hexagon.
No parameter search, guessed support list, or spectral premise is used. -/

set_option autoImplicit false
noncomputable section

namespace Paper7C61Three

open BackfillPaper7.Challenge
open scoped Classical

theorem alpha_six_even_gap (p : Fin 6 → ℕ)
    (h : Paper7C61Profile.zeroExponent p = 6) (k : Fin 6) (hk : 0 < p k) :
    ∃ d ∈ Finset.Icc 1 6, Even d ∧ ((finRotate 6) ^ d) k ∈ Kp 6 p ∧
      ∀ d' ∈ Finset.Ico 1 d, ((finRotate 6) ^ d') k ∉ Kp 6 p := by
  have hkK : k ∈ Kp 6 p := by simp only [Kp, Finset.mem_filter,
    Finset.mem_univ, true_and]; exact hk
  have hK : Kp 6 p ≠ ∅ := by
    intro he
    rw [he] at hkK
    exact Finset.notMem_empty k hkK
  have hc : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  have hd : delta0 6 p = (Kp 6 p).card := by
    unfold Paper7C61Profile.zeroExponent at h
    omega
  rw [delta0, ite_eq_right hK] at hd
  unfold evenGaps at hd
  exact Finset.card_filter_eq_iff.mp hd k hkK

#print axioms Paper7C61Three.alpha_six_even_gap

theorem alpha_six_successor_zero (p : Fin 6 → ℕ)
    (h : Paper7C61Profile.zeroExponent p = 6) (k : Fin 6) (hk : 0 < p k) :
    p (k + 1) = 0 := by
  obtain ⟨d, hd, he, _hend, hclear⟩ := alpha_six_even_gap p h k hk
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hd2 : 2 ≤ d := by
    obtain ⟨t, ht⟩ := he
    omega
  have hz := hclear 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hr : ((finRotate 6) ^ (1 : ℕ)) k = k + (1 : Fin 6) := by
    simp
  rw [hr] at hz
  have hn : ¬ 0 < p (k + 1) := by
    simpa only [Kp, Finset.mem_filter, Finset.mem_univ, true_and] using hz
  omega

#print axioms Paper7C61Three.alpha_six_successor_zero

theorem alpha_six_antipode_zero (p : Fin 6 → ℕ)
    (h : Paper7C61Profile.zeroExponent p = 6) (k : Fin 6) (hk : 0 < p k) :
    p (k + 3) = 0 := by
  by_contra hn
  have hop : 0 < p (k + 3) := Nat.pos_of_ne_zero hn
  have hz4 : p (k + 4) = 0 := by
    have hz := alpha_six_successor_zero p h (k + 3) hop
    simpa only [add_assoc, show (3 : Fin 6) + 1 = 4 from rfl] using hz
  have hz2 : p (k + 2) = 0 := by
    by_contra hn2
    have hz := alpha_six_successor_zero p h (k + 2) (Nat.pos_of_ne_zero hn2)
    have hz3 : p (k + 3) = 0 := by
      simpa only [add_assoc, show (2 : Fin 6) + 1 = 3 from rfl] using hz
    omega
  obtain ⟨d, hd, he, hend, hclear⟩ := alpha_six_even_gap p h k hk
  have hdl := (Finset.mem_Icc.mp hd).1
  have hdu := (Finset.mem_Icc.mp hd).2
  have hcases : d = 2 ∨ d = 4 ∨ d = 6 := by
    obtain ⟨t, ht⟩ := he
    omega
  rcases hcases with rfl | rfl | rfl
  · have hr : ((finRotate 6) ^ (2 : ℕ)) k = k + (2 : Fin 6) := by
      simpa using Paper7C61Orbit.rotationPower_apply (2 : Fin 6) k
    rw [hr] at hend
    have hp2 : 0 < p (k + 2) := by
      simpa only [Kp, Finset.mem_filter, Finset.mem_univ, true_and] using hend
    omega
  · have hr : ((finRotate 6) ^ (4 : ℕ)) k = k + (4 : Fin 6) := by
      simpa using Paper7C61Orbit.rotationPower_apply (4 : Fin 6) k
    rw [hr] at hend
    have hp4 : 0 < p (k + 4) := by
      simpa only [Kp, Finset.mem_filter, Finset.mem_univ, true_and] using hend
    omega
  · have hz := hclear 3 (by decide)
    have hr : ((finRotate 6) ^ (3 : ℕ)) k = k + (3 : Fin 6) := by
      simpa using Paper7C61Orbit.rotationPower_apply (3 : Fin 6) k
    rw [hr] at hz
    apply hz
    simpa only [Kp, Finset.mem_filter, Finset.mem_univ, true_and] using hop

#print axioms Paper7C61Three.alpha_six_antipode_zero

theorem alpha_six_opposite_parity_zero (p : Fin 6 → ℕ)
    (h : Paper7C61Profile.zeroExponent p = 6) (k : Fin 6) (hk : 0 < p k) :
    p (k + 1) = 0 ∧ p (k + 3) = 0 ∧ p (k + 5) = 0 := by
  refine ⟨alpha_six_successor_zero p h k hk, alpha_six_antipode_zero p h k hk, ?_⟩
  by_contra hn
  have hz := alpha_six_successor_zero p h (k + 5) (Nat.pos_of_ne_zero hn)
  have hz0 : p k = 0 := by
    simpa only [add_assoc, show (5 : Fin 6) + 1 = 0 from rfl, add_zero] using hz
  omega

#print axioms Paper7C61Three.alpha_six_opposite_parity_zero

theorem alpha_six_parity (p : Fin 6 → ℕ)
    (h : Paper7C61Profile.zeroExponent p = 6) :
    (p 1 = 0 ∧ p 3 = 0 ∧ p 5 = 0) ∨ (p 0 = 0 ∧ p 2 = 0 ∧ p 4 = 0) := by
  by_cases h0 : p 0 = 0
  · by_cases h2 : p 2 = 0
    · by_cases h4 : p 4 = 0
      · exact Or.inr ⟨h0, h2, h4⟩
      · have hz := alpha_six_opposite_parity_zero p h 4 (Nat.pos_of_ne_zero h4)
        change p 5 = 0 ∧ p 1 = 0 ∧ p 3 = 0 at hz
        exact Or.inl ⟨hz.2.1, hz.2.2, hz.1⟩
    · have hz := alpha_six_opposite_parity_zero p h 2 (Nat.pos_of_ne_zero h2)
      change p 3 = 0 ∧ p 5 = 0 ∧ p 1 = 0 at hz
      exact Or.inl ⟨hz.2.2, hz.1, hz.2.1⟩
  · have hz := alpha_six_opposite_parity_zero p h 0 (Nat.pos_of_ne_zero h0)
    change p 1 = 0 ∧ p 3 = 0 ∧ p 5 = 0 at hz
    exact Or.inl hz

#print axioms Paper7C61Three.alpha_six_parity

end Paper7C61Three
