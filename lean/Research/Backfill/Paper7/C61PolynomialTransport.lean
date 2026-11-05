import Research.Backfill.Paper7.C61SaturatedParameters
import Research.Backfill.Paper7.GraphPhiCharpoly

set_option autoImplicit false
noncomputable section
namespace Paper7C61Saturated
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem graphPhi_iso {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) : graphPhi H = graphPhi G := by
  rw [Paper7GraphPhi.graphPhi_eq_charpoly, Paper7GraphPhi.graphPhi_eq_charpoly,
    ← e.reindex_adjMatrix ℤ]
  exact Matrix.charpoly_reindex e.toEquiv (G.adjMatrix ℤ)
#print axioms Paper7C61Saturated.graphPhi_iso

theorem graphPhi_comp (p q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) :
    graphPhi (SG 6 (p ∘ σ) (q ∘ σ)) = graphPhi (SG 6 p q) := by
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 6 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  exact graphPhi_iso _ _ e
#print axioms Paper7C61Saturated.graphPhi_comp

theorem clearedF_comp (p q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) : clearedF 6 (p ∘ σ) (q ∘ σ) = clearedF 6 p q := by
  have hbij := Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ
  have hP : totalP 6 (p ∘ σ) = totalP 6 p := hbij.sum_comp p
  have hQ : totalQ 6 (q ∘ σ) = totalQ 6 q := hbij.sum_comp q
  have hn : (X ^ totalP 6 p * (X ^ 2 - 1) ^ totalQ 6 q : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor (totalP 6 p) (totalQ 6 q)).ne_zero
  apply mul_left_cancel₀ hn
  calc
    _ = X ^ 6 * (X ^ 2 - 1) ^ 6 * graphPhi (SG 6 (p ∘ σ) (q ∘ σ)) := by
      simpa only [hP, hQ] using
        Paper7Cleared.cleared_identity 6 (p ∘ σ) (q ∘ σ) (by decide)
    _ = X ^ 6 * (X ^ 2 - 1) ^ 6 * graphPhi (SG 6 p q) := by rw [graphPhi_comp p q σ hσ]
    _ = _ := (Paper7Cleared.cleared_identity 6 p q (by decide)).symm
#print axioms Paper7C61Saturated.clearedF_comp

def target : Polynomial ℤ :=
  X ^ 2 * (X ^ 2 - 1) ^ 6 * ((X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16))
#print axioms Paper7C61Saturated.target

theorem saturated_normalized_polynomial (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : Paper7C61Profile.card (Paper7C61Profile.actual p q) = 5) :
    q = (fun _ => 0) ∧ ∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ (p ∘ σ) 0 = 0 ∧
      (∀ k, k ≠ 0 → 3 ≤ (p ∘ σ) k ∧ (p ∘ σ) k ≤ 12) ∧
      totalP 6 (p ∘ σ) = 36 ∧ Paper7C61Parameters.squares 6 (p ∘ σ) = 288 ∧
      clearedF 6 (p ∘ σ) (fun _ => 0) = target := by
  obtain ⟨hq, σ, hσ, hz, hi, hP, hS, _hI⟩ :=
    Paper7C61Parameters.saturated_normalized_parameters p q hp hn hG hc
  obtain ⟨_hm, _hn, _hu, _hQ, _hPQ, _ha, _he, hF⟩ :=
    Paper7C61Profile.saturated_profile_parameters p q hp hn hG hc
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have hpoly : clearedF 6 p q = target := by simpa only [target, hQ, mul_zero, add_zero,
    Nat.sub_zero] using hF
  have ht := clearedF_comp p q σ hσ
  have hqt : q ∘ σ = (fun _ => 0) := by rw [hq]; rfl
  rw [hqt] at ht
  exact ⟨hq, σ, hσ, hz, hi, hP, hS, ht.trans hpoly⟩
#print axioms Paper7C61Saturated.saturated_normalized_polynomial

end Paper7C61Saturated
