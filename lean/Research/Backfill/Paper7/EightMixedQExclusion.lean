import Research.Backfill.Paper7.EightMixedLoadBounds
import Research.Backfill.Paper7.EightPuncturedUnitPaths

/-! NEW SOURCE ONLY. Complete exclusion of the mixed eight-cycle branch.
The saturated actual Wmat kernel supplies a punctured unit recurrence. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_alternating_mixed_nonintegral (p q : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hn : nOf 8 p q ≤ 41) :
    ¬ IsIntegralGraph (SG 8 p q) := by
  intro hG
  obtain ⟨hP,hcap⟩ := eight_mixed_load_data p q hp hq hn hG
  obtain ⟨_hc,_hd,hplus,_hminus,_hu,_hS⟩ := eight_mixed_rank_saturated p q hp hq hn hG
  have hK : (Kq 8 q).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 q (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  obtain ⟨k,hk⟩ := hK
  obtain ⟨y,hy,hyk,hr⟩ := saturated_unit_punctured_solution p q hplus k hk
  have hsmall := alternating_punctured_load p ho (fun i => by have := hcap i; omega)
    y hy k hyk hr
  omega
#print axioms Paper7EightCycle.eight_alternating_mixed_nonintegral

theorem eight_mixed_nonintegral (p q : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hn : nOf 8 p q ≤ 41) :
    ¬ IsIntegralGraph (SG 8 p q) := by
  intro hG
  obtain ⟨_hc,hd,_hplus,_hminus,_hu,_hS⟩ := eight_mixed_rank_saturated p q hp hq hn hG
  obtain ⟨k,hk⟩ : ∃ k : Fin 8, 0 < p k := by
    by_contra hh
    push Not at hh
    have hz : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => by have := hh i; omega)
    omega
  let σ : Fin 8 → Fin 8 := fun i => i+k
  have hσ : IsDihedral 8 σ := by refine ⟨k,Or.inl ?_⟩; intro i; rfl
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 8 p q
    (p ∘ σ) (q ∘ σ) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hbij := Paper7PruningCanonical.dihedral_bijective 8 (by decide) σ hσ
  have hsumP : ∑ i, (p ∘ σ) i = ∑ i, p i := hbij.sum_comp p
  have hsumQ : ∑ i, (q ∘ σ) i = ∑ i, q i := hbij.sum_comp q
  have hp' : 0 < ∑ i, (p ∘ σ) i := by rw [hsumP]; exact hp
  have hq' : 0 < ∑ i, (q ∘ σ) i := by rw [hsumQ]; exact hq
  have hn' : nOf 8 (p ∘ σ) (q ∘ σ) ≤ 41 := by
    simpa only [nOf,hsumP,hsumQ] using hn
  have ho' : ∀ i : Fin 8, Odd i.val → (p ∘ σ) i = 0 :=
    eight_saturated_rotated_odd_zero p hd k hk
  exact eight_alternating_mixed_nonintegral (p ∘ σ) (q ∘ σ) ho' hp' hq' hn' hI
#print axioms Paper7EightCycle.eight_mixed_nonintegral

end Paper7EightCycle
