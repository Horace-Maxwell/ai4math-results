import Research.Backfill.Paper6.ChallengeV3

/-!
# Structured finite data facts for the frozen Paper 6 V3 contract

Candidate proof source, not yet compiled or accepted. The interval is counted through
an injective parametrization; no decision procedure enumerates the 16065-element range.
The small decisions concern K (18 entries), its image, U (8 entries), and IntroMU.
These facts do not assert that any listed integer is a Reed–Muller weight.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6FiniteFacts

open BackfillPaper6.V3

theorem check_S0_card : BackfillPaper6.V3.S0_card := by
  let I : Finset ℕ := (Finset.range 16065).filter (fun w => 320 ≤ w ∧ Even w)
  let C : Finset ℕ := K.image (fun k => 16384 - k)
  have memI (w : ℕ) : w ∈ I ↔ w < 16065 ∧ 320 ≤ w ∧ Even w := by
    simp only [I, Finset.mem_filter, Finset.mem_range]
  have interval_eq : I = (Finset.range 7873).image (fun n => 2 * n + 320) := by
    ext w
    rw [memI w]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hwmax, hwmin, heven⟩
      obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
      refine ⟨k - 160, ?_, ?_⟩ <;> omega
    · rintro ⟨n, hn, rfl⟩
      refine ⟨by omega, by omega, ?_⟩
      exact even_iff_exists_two_mul.mpr ⟨n + 160, by omega⟩
  have parametrization_injective : Function.Injective (fun n : ℕ => 2 * n + 320) := by
    intro a b hab
    change 2 * a + 320 = 2 * b + 320 at hab
    omega
  have interval_card : I.card = 7873 := by
    rw [interval_eq, Finset.card_image_of_injective _ parametrization_injective,
      Finset.card_range]
  have K_card : K.card = 18 := by decide +kernel
  have K_bound : ∀ k ∈ K, k ≤ 318 := by decide +kernel
  have C_card : C.card = 18 := by
    change (K.image (fun k => 16384 - k)).card = 18
    decide +kernel
  have C_bound : ∀ c ∈ C, 16064 < c := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    have hbound := K_bound k hk
    omega
  have K_I_disjoint : Disjoint K I := by
    apply Finset.disjoint_left.mpr
    intro w hwK hwI
    have hlow := K_bound w hwK
    have hhigh := (memI w).mp hwI
    omega
  have KI_C_disjoint : Disjoint (K ∪ I) C := by
    apply Finset.disjoint_left.mpr
    intro w hwKI hwC
    have hhigh := C_bound w hwC
    rcases Finset.mem_union.mp hwKI with hwK | hwI
    · have hlow := K_bound w hwK
      omega
    · have hlow := (memI w).mp hwI
      omega
  have all_card : ((K ∪ I) ∪ C).card = 7909 := by
    rw [Finset.card_union_of_disjoint KI_C_disjoint,
      Finset.card_union_of_disjoint K_I_disjoint, K_card, interval_card, C_card]
  have U_card : U.card = 8 := by decide +kernel
  have U_bounds : ∀ w ∈ U, w < 16065 ∧ 320 ≤ w ∧ Even w := by decide +kernel
  have U_subset : U ⊆ (K ∪ I) ∪ C := by
    intro w hwU
    exact Finset.mem_union_left C (Finset.mem_union_right K
      ((memI w).mpr (U_bounds w hwU)))
  change (((K ∪ I) ∪ C) \ U).card = 7901
  rw [Finset.card_sdiff_of_subset U_subset, all_card, U_card]

theorem check_IntroMU : BackfillPaper6.V3.IntroMU := by
  unfold BackfillPaper6.V3.IntroMU
  decide +kernel

end Paper6FiniteFacts

#print axioms Paper6FiniteFacts.check_S0_card
#print axioms Paper6FiniteFacts.check_IntroMU
