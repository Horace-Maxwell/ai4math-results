import Research.TaskS.B.KernelRounding
import Research.TaskS.Shared.Sawtooth

open scoped BigOperators
open Module Finset
namespace TaskS.B.Upper

theorem round_matrix {m i : ℕ} [Nonempty (Fin m)] (A : Matrix (Fin i) (Fin m) ℤ)
    (hbal : ∀ k, ∑ j, A k j = 0) (x : Fin m → ℝ) :
    ∃ h : Fin m → ℝ, (∀ k, ∑ j, (A k j : ℝ) * h j = 0) ∧
      (∑ j, Int.fract (x j + h j)) ≤ (i : ℝ)/2 := by
  let f := (A.map (Int.castRingHom ℚ)).mulVecLin
  let g := (A.map (Int.castRingHom ℝ)).mulVecLin
  have hz : (fun _ => (1 : ℚ)) ∈ LinearMap.ker f := by
    apply LinearMap.mem_ker.mpr
    ext k
    change (∑ j, (A k j : ℚ) * 1) = 0
    simp only [mul_one]
    exact_mod_cast hbal k
  have hc : Rounding.CastsInto (LinearMap.ker f) (LinearMap.ker g) := by
    intro z hz
    apply LinearMap.mem_ker.mpr
    ext k
    have hz' := congrFun (LinearMap.mem_ker.mp hz) k
    change (∑ j, (A k j : ℚ) * z j) = 0 at hz'
    change (∑ j, (A k j : ℝ) * (z j : ℝ)) = 0
    exact_mod_cast hz'
  obtain ⟨h, hh, hb⟩ := Rounding.round (fun _ _ _ => TaskS.Shared.sawtooth_unweighted)
    (Fin m) _ _ hc ⟨_,hz⟩ (fun _ => zero_lt_one) x
  refine ⟨h, fun k => congrFun (LinearMap.mem_ker.mp hh) k, hb.trans ?_⟩
  have hr := f.finrank_range_add_finrank_ker
  have hi := (LinearMap.range f).finrank_le
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at *
  have hr' : (finrank ℚ (LinearMap.range f) : ℝ) + (finrank ℚ (LinearMap.ker f) : ℝ) = m := by exact_mod_cast hr
  have hi' : (finrank ℚ (LinearMap.range f) : ℝ) ≤ i := by exact_mod_cast hi
  linarith

end TaskS.B.Upper
