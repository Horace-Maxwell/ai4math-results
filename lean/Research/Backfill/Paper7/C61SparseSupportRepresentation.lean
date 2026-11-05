import Research.Backfill.Paper7.C61ParameterSquares

/-! Padding a support to three or four actual positions preserves both
moments. No parameter list or numerical search is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Sparse
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters
open scoped BigOperators Classical

theorem moments_on_support_superset (p : Fin 6 → ℕ) (S : Finset (Fin 6))
    (hS : Kp 6 p ⊆ S) :
    (∑ k ∈ S, p k) = totalP 6 p ∧ (∑ k ∈ S, p k^2) = squares 6 p := by
  have hz (k : Fin 6) (hk : k ∉ S) : p k = 0 := by
    have hnot : ¬ 0 < p k := by
      intro hp
      exact hk (hS (Finset.mem_filter.mpr ⟨Finset.mem_univ k,hp⟩))
    omega
  constructor
  · apply Finset.sum_subset (Finset.subset_univ S)
    intro k _hk hk
    exact hz k hk
  · apply Finset.sum_subset (Finset.subset_univ S)
    intro k _hk hk
    rw [hz k hk]
    norm_num
#print axioms Paper7C61Sparse.moments_on_support_superset

theorem support_three_moments (p : Fin 6 → ℕ) (hK : (Kp 6 p).card ≤ 3) :
    ∃ a b c : ℤ, a+b+c = totalP 6 p ∧ a^2+b^2+c^2 = squares 6 p := by
  obtain ⟨S,hKS,_hSU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Kp 6 p)) hK (by simp : 3 ≤ (Finset.univ : Finset (Fin 6)).card)
  obtain ⟨i,j,k,hij,hik,hjk,hS⟩ := Finset.card_eq_three.mp hcard
  obtain ⟨hs,hq⟩ := moments_on_support_superset p S hKS
  rw [hS] at hs hq
  simp [hij,hik,hjk] at hs hq
  refine ⟨p i,p j,p k,?_,?_⟩
  · exact_mod_cast (by omega : p i+p j+p k = totalP 6 p)
  · exact_mod_cast (by omega : p i^2+p j^2+p k^2 = squares 6 p)
#print axioms Paper7C61Sparse.support_three_moments

theorem support_four_moments (p : Fin 6 → ℕ) (hK : (Kp 6 p).card ≤ 4) :
    ∃ a b c d : ℤ, a+b+c+d = totalP 6 p ∧ a^2+b^2+c^2+d^2 = squares 6 p := by
  obtain ⟨S,hKS,_hSU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Kp 6 p)) hK (by simp : 4 ≤ (Finset.univ : Finset (Fin 6)).card)
  obtain ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,hS⟩ := Finset.card_eq_four.mp hcard
  obtain ⟨hs,hq⟩ := moments_on_support_superset p S hKS
  rw [hS] at hs hq
  simp [hij,hik,hil,hjk,hjl,hkl] at hs hq
  refine ⟨p i,p j,p k,p l,?_,?_⟩
  · exact_mod_cast (by omega : p i+p j+p k+p l = totalP 6 p)
  · exact_mod_cast (by omega : p i^2+p j^2+p k^2+p l^2 = squares 6 p)
#print axioms Paper7C61Sparse.support_four_moments

theorem totalQ_one_coordinate (q : Fin 6 → ℕ) (hQ : totalQ 6 q = 1) :
    ∃ t : Fin 6, q t = 1 ∧ ∀ k, k ≠ t → q k = 0 := by
  obtain ⟨t,ht⟩ : ∃ t, 0 < q t := by
    by_contra! h
    have hz : totalQ 6 q = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      exact Nat.eq_zero_of_le_zero (h k)
    omega
  have hle : q t ≤ totalQ 6 q :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (q k)) (Finset.mem_univ t)
  have ht1 : q t = 1 := by omega
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) q (Finset.mem_univ t)
  change (∑ k ∈ Finset.univ.erase t, q k) + q t = totalQ 6 q at he
  have hz : (∑ k ∈ Finset.univ.erase t, q k) = 0 := by omega
  refine ⟨t,ht1,?_⟩
  intro k hkt
  have hk : k ∈ Finset.univ.erase t := Finset.mem_erase.mpr ⟨hkt,Finset.mem_univ k⟩
  have hkq := Finset.single_le_sum (fun i _ => Nat.zero_le (q i)) hk
  rw [hz] at hkq
  omega
#print axioms Paper7C61Sparse.totalQ_one_coordinate

end Paper7C61Sparse
