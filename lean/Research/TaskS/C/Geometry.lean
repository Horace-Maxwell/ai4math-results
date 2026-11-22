import Research.TaskS.C.Frequencies
import Research.TaskS.C.Lift
import Research.TaskS.C.Projected

namespace TaskS.C

open Challenge
open scoped BigOperators

theorem geometry {n : ℕ} (u : Fin (n+2) → Challenge.Lattice (n+1)) (ω : Fin (n+2) → ℝ)
    (hω : ∀ i, 0 < ω i) (hv : 0 < volume (vertices u ω))
    (hi : (0 : Space (n+1)) ∈ interior (simplex (vertices u ω)))
    (round : ∀ (q : Fin (n+2) → ℕ), (∀ i, 0 < q i) →
      ∀ x : Fin (n+2) → ℝ, ∃ t : ℝ,
        (∑ i, (1/ω i) * Int.fract (x i + (q i : ℝ) * t)) ≤
          ((∑ i, 1/ω i) - (∑ i, (q i : ℝ) * (1/ω i)^2) / (∑ i, (q i : ℝ) * (1/ω i)))/2) :
    Covers (simplex (vertices u ω)) ((∑ i, projectedVolume (vertices u ω) u i) /
      (2 * volume (vertices u ω))) := by
  let v := vertices u ω
  obtain ⟨β, hβ, hs, hz, hspan⟩ := coordinates v hi
  let q := frequency u
  let m := volume v / ∏ i, ω i
  have hprod : 0 < ∏ i, ω i := Finset.prod_pos fun i _ => hω i
  have hm : 0 < m := div_pos hv hprod
  have hformula (i) : (q i : ℝ) = m * β i * ω i := by
    have he := frequency_ratio u ω β hω hβ hs hz i
    dsimp only [q, m, v]
    field_simp [hprod.ne']
    linarith [he]
  have hqpos (i) : 0 < q i := by
    have : (0 : ℝ) < q i := by rw [hformula]; exact mul_pos (mul_pos hm (hβ i)) (hω i)
    exact_mod_cast this
  have hkernel : ∑ i, (q i : ℝ) • embed (u i) = 0 := by
    calc
      _ = ∑ i, m • (β i • v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hformula]
        simp only [v, vertices, smul_smul, mul_assoc]
      _ = 0 := by rw [← Finset.smul_sum, hz, smul_zero]
  have hW : (∑ i, (q i : ℝ) * (1 / ω i)) = m := by
    calc
      _ = ∑ i, m * β i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hformula]
        field_simp [(hω i).ne']
      _ = m := by rw [← Finset.mul_sum, hs, mul_one]
  have hE : (∑ i, (q i : ℝ) * (1 / ω i)^2) = m * ∑ i, β i / ω i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hformula]
    field_simp [(hω i).ne']
  let r := (∑ i, (1 - β i) / ω i)/2
  have hR : ((∑ i, 1 / ω i) - (∑ i, (q i : ℝ) * (1 / ω i)^2) /
      (∑ i, (q i : ℝ) * (1 / ω i)))/2 = r := by
    rw [hW, hE, mul_div_cancel_left₀ _ hm.ne', ← Finset.sum_sub_distrib]
    simp [r, sub_div]
  have hβlt (i) : β i < 1 := by
    have hrest := Finset.sum_pos (s := Finset.univ) (fun j _ => hβ (i.succAbove j))
      Finset.univ_nonempty
    rw [Fin.sum_univ_succAbove β i] at hs
    linarith
  have hr : 0 < r := div_pos (Finset.sum_pos
    (fun i _ => div_pos (sub_pos.mpr (hβlt i)) (hω i)) Finset.univ_nonempty) (by norm_num)
  have hscale : (∑ i, projectedVolume v u i) / (2 * volume v) = r := by
    simp_rw [v, projected_eq u ω β hω hβ hs hz]
    rw [← Finset.mul_sum]
    dsimp only [r, v]
    field_simp [hv.ne']
  rw [show ((∑ i, projectedVolume (vertices u ω) u i) /
      (2 * volume (vertices u ω))) = r from hscale]
  apply rounded_cover u ω β hω hβ hs hz hspan q hkernel hr
  intro x
  obtain ⟨t, ht⟩ := round q hqpos x
  exact ⟨t, hR ▸ ht⟩

end TaskS.C
