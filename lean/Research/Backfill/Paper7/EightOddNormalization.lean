import Research.Backfill.Paper7.EightParameterCover
import Research.Backfill.Paper7.EightCoreParity
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! Source-only normalization of the actual two odd sites. The odd-support
condition in the mod-two helper is proved here from the two moments. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_integral_odd_support_two (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    (Finset.univ.filter (fun i : Fin 8 => p i % 2 = 1)).card = 2 := by
  have hf : ((pBag p).map (fun n : ℕ => if n % 2 = 1 then (1 : ℕ) else 0)).sum = 2 := by
    rcases eight_integral_parameter_cover p hp hn hG with h|h|h|h <;> rw [h] <;> norm_num
  have hmap (f : ℕ → ℕ) : ((pBag p).map f).sum = ∑ i : Fin 8, f (p i) := by
    simp only [pBag, Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  have hs : (∑ i : Fin 8, if p i % 2 = 1 then 1 else 0 : ℕ) = 2 :=
    (hmap (fun n => if n % 2 = 1 then 1 else 0)).symm.trans hf
  exact (Finset.sum_boole (R := ℕ) (fun i : Fin 8 => p i % 2 = 1) Finset.univ).symm.trans hs
#print axioms Paper7EightCycle.eight_integral_odd_support_two

theorem eight_integral_odd_normalization (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    ∃ p' : Fin 8 → ℕ, (∑ i, p' i) = (∑ i, p i) ∧
      nOf 8 p' (fun _ => 0) ≤ 41 ∧ IsIntegralGraph (SG 8 p' (fun _ => 0)) ∧
      (∀ i : Fin 8, (p' i : ZMod 2) = if i = 0 ∨ i = 4 then 1 else 0) := by
  obtain ⟨k,j,hkj,hs⟩ := Finset.card_eq_two.mp (eight_integral_odd_support_two p hp hn hG)
  have hodd (i : Fin 8) : p i % 2 = 1 ↔ i = k ∨ i = j := by
    have hh : i ∈ Finset.univ.filter (fun i : Fin 8 => p i % 2 = 1) ↔ i ∈ ({k,j} : Finset (Fin 8)) := by
      rw [hs]
    simpa using hh
  let σ : Fin 8 → Fin 8 := fun i => i+k
  have hσ : IsDihedral 8 σ := by refine ⟨k,Or.inl ?_⟩; intro i; rfl
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 8 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hbij := Paper7PruningCanonical.dihedral_bijective 8 (by decide) σ hσ
  have hsum : ∑ i, (p ∘ σ) i = ∑ i, p i := hbij.sum_comp p
  have hn' : nOf 8 (p ∘ σ) (fun _ => 0) ≤ 41 := by simpa only [nOf,hsum] using hn
  have hp' : 0 < ∑ i, (p ∘ σ) i := by rw [hsum]; exact hp
  have hj : j-k ≠ 0 := by
    intro hh
    have heq : j = k := sub_eq_zero.mp hh
    exact hkj heq.symm
  have hor (i : Fin 8) : (p ∘ σ) i % 2 = 1 ↔ i = 0 ∨ i = j-k := by
    change p (i+k) % 2 = 1 ↔ _
    rw [hodd]
    constructor
    · rintro (hi|hi)
      · left
        exact add_right_cancel (hi.trans (zero_add k).symm)
      · exact Or.inr (eq_sub_iff_add_eq.mpr hi)
    · rintro (rfl|hi)
      · exact Or.inl (zero_add k)
      · exact Or.inr (eq_sub_iff_add_eq.mp hi)
  have hpar : ∀ i : Fin 8, ((p ∘ σ) i : ZMod 2) =
      if i = 0 ∨ i = j-k then 1 else 0 := by
    intro i
    by_cases hi : i = 0 ∨ i = j-k
    · rw [ite_eq_left hi]
      have hm := (hor i).mpr hi
      simpa using (ZMod.natCast_eq_natCast_iff' ((p ∘ σ) i) 1 2).mpr (by simpa using hm)
    · rw [ite_eq_right hi]
      have hno : ¬ (p ∘ σ) i % 2 = 1 := fun hm => hi ((hor i).mp hm)
      have hm : (p ∘ σ) i % 2 = 0 := by have := Nat.mod_lt ((p ∘ σ) i) (by decide : 0 < 2); omega
      simpa using (ZMod.natCast_eq_natCast_iff' ((p ∘ σ) i) 0 2).mpr (by simpa using hm)
  have hop := eight_integral_two_odd_opposite (p ∘ σ) hp' hn' hI (j-k) hj hpar
  exact ⟨p ∘ σ,hsum,hn',hI,by simpa only [hop] using hpar⟩
#print axioms Paper7EightCycle.eight_integral_odd_normalization

end Paper7EightCycle
