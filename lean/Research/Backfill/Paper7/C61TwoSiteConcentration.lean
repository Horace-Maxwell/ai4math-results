import Research.Backfill.Paper7.C61RootThreeReduction

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters
open scoped BigOperators Classical

theorem sum9_square45_two_sites (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 9) (hS : squares 6 p = 45) :
    ∃ k j : Fin 6, j ≠ k ∧ p k = 6 ∧ p j = 3 ∧
      ∀ i, i ≠ k → i ≠ j → p i = 0 := by
  obtain ⟨k,hk,hA,hB⟩ := sum9_square45_maximum p hP hS
  have hex : ∃ j ∈ Finset.univ.erase k, p j = 3 := by
    by_contra h
    have hle : (∑ j ∈ Finset.univ.erase k, p j^2) ≤
        2*(∑ j ∈ Finset.univ.erase k, p j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hsmall : p j ≤ 3 := by
        have hb := Finset.single_le_sum (fun i _ => Nat.zero_le (p i)) hj
        rwa [hA] at hb
      have hne : p j ≠ 3 := fun hpj => h ⟨j,hj,hpj⟩
      have htwo : p j ≤ 2 := by omega
      nlinarith
    omega
  obtain ⟨j,hj,hpj⟩ := hex
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hrest := Finset.sum_erase_add (Finset.univ.erase k) p hj
  rw [hA,hpj] at hrest
  have hrest0 : (∑ i ∈ (Finset.univ.erase k).erase j, p i) = 0 := by omega
  refine ⟨k,j,hjk,hk,hpj,?_⟩
  intro i hik hij
  have hi : i ∈ (Finset.univ.erase k).erase j :=
    Finset.mem_erase.mpr ⟨hij, Finset.mem_erase.mpr ⟨hik,Finset.mem_univ _⟩⟩
  have hle := Finset.single_le_sum (fun x _ => Nat.zero_le (p x)) hi
  rw [hrest0] at hle
  omega
#print axioms Paper7C61Small.sum9_square45_two_sites

def twoSite (j : Fin 6) : Fin 6 → ℕ :=
  fun i => if i = 0 then 6 else if i = j then 3 else 0
#print axioms Paper7C61Small.twoSite

theorem two_sites_normalize (p : Fin 6 → ℕ) (k j : Fin 6) (hjk : j ≠ k)
    (hk : p k = 6) (hj : p j = 3) (hz : ∀ i, i ≠ k → i ≠ j → p i = 0) :
    ∃ (σ : Fin 6 → Fin 6) (t : Fin 6), IsDihedral 6 σ ∧ t ≠ 0 ∧ p ∘ σ = twoSite t := by
  obtain ⟨σ,hσ,hσ0⟩ := Paper7PruningCanonical.dihedral_rotation_to 6 (by decide) k 0 rfl
  have hbij := Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ
  obtain ⟨t,ht⟩ := hbij.2 j
  have ht0 : t ≠ 0 := by
    intro heq
    rw [heq,hσ0] at ht
    exact hjk ht.symm
  refine ⟨σ,t,hσ,ht0,?_⟩
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp only [Function.comp_apply,twoSite,ite_true,hσ0,hk]
  · by_cases hit : i = t
    · subst i
      simp only [Function.comp_apply,twoSite,ht0,ite_false,ite_true,ht,hj]
    · have hik : σ i ≠ k := by
        intro h
        exact hi0 (hbij.1 (h.trans hσ0.symm))
      have hij : σ i ≠ j := by
        intro h
        exact hit (hbij.1 (h.trans ht.symm))
      simp only [Function.comp_apply,twoSite,hi0,hit,ite_false,hz (σ i) hik hij]
#print axioms Paper7C61Small.two_sites_normalize

end Paper7C61Small
