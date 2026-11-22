import Mathlib

open Set Metric Filter
open scoped Topology

namespace TaskP.GraphRootRadius.Proof

/-- A strict dip at the center forces a zero by the maximum principle for the reciprocal. -/
theorem zero_of_dip {f : ℂ → ℂ} {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DiffContOnCl ℂ f (ball x r))
    (h : ∀ w ∈ sphere x r, ‖f x‖ < ‖f w‖) :
    ∃ w ∈ closedBall x r, f w = 0 := by
  by_contra! hn
  have hi : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball x r) := hd.inv (by
    rwa [closure_ball x hr.ne'])
  obtain ⟨w,hw,hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
    (nonempty_ball.mpr hr) hi
  rw [frontier_ball x hr.ne'] at hw
  have hm := hmax (subset_closure (mem_ball_self hr))
  change ‖(f x)⁻¹‖ ≤ ‖(f w)⁻¹‖ at hm
  rw [norm_inv, norm_inv] at hm
  exact (not_le_of_gt (inv_lt_inv₀ (norm_pos_iff.mpr (hn w (sphere_subset_closedBall hw)))
    (norm_pos_iff.mpr (hn x (mem_closedBall_self hr.le))) |>.mpr (h w hw))) hm

/-- The filter on the parameter may be at infinity. Compactness makes the local
eventual assertions simultaneous for all points of K. -/
theorem compact_eventually {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {K : Set X} (hK : IsCompact K) {P : ι → X → Prop}
    (h : ∀ x ∈ K, ∀ᶠ z : ι × X in l ×ˢ 𝓝 x, P z.1 z.2) :
    ∀ᶠ i in l, ∀ x ∈ K, P i x := by
  have ht : ∀ᶠ z : ι × X in l ×ˢ 𝓝ˢ K, P z.1 z.2 := by
    simpa only [hK.prod_nhdsSet_eq_biSup, eventually_iSup] using h
  exact ht.curry.mono fun _ hi => hi.self_of_nhdsSet

theorem eventual_zero_of_dip {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ}
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ᶠ i in l, DiffContOnCl ℂ (F i) (ball x r))
    (hcenter : Tendsto (fun i => F i x) l (𝓝 0))
    (hlim : ∀ w ∈ sphere x r, ∃ y : ℂ, y ≠ 0 ∧
      Tendsto (fun p : ι × ℂ => F p.1 p.2) (l ×ˢ 𝓝 w) (𝓝 y)) :
    ∀ᶠ i in l, ∃ w ∈ closedBall x r, F i w = 0 := by
  have hbd : ∀ᶠ i in l, ∀ w ∈ sphere x r, ‖F i x‖ < ‖F i w‖ := by
    apply compact_eventually (isCompact_sphere x r)
    intro w hw
    obtain ⟨y,hy,h⟩ := hlim w hw
    apply Filter.Tendsto.eventually_lt ((hcenter.comp tendsto_fst).norm) h.norm
    simpa using norm_pos_iff.mpr hy
  filter_upwards [hd,hbd] with i hi he using zero_of_dip hr hi he

end TaskP.GraphRootRadius.Proof
