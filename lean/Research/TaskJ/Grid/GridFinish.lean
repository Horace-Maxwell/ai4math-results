import Research.TaskJ.Grid.GridUpperComplete

namespace Grid.Finish

open Challenge

/-- Transfer normalized attainment along the isometry that restores every unit axis. -/
theorem restore (normalized : ∀ ds : List ℕ, (∀ d ∈ ds, 1 < d) →
    ∃ p, Order ds p ∧ (pathLength p : ℤ) = optimumFormula ds) : LengthAttained := by
  intro ds h
  have wide : ∀ d ∈ Transport.effective ds, 1 < d := by
    intro d hd
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp hd
    have hpos := h d hmem
    have hne' : d ≠ 1 := by simpa using hne
    omega
  obtain ⟨p,hp,hlen⟩ := normalized (Transport.effective ds) wide
  obtain ⟨back⟩ := (Transport.strip_maps ds).2
  obtain ⟨q,hq,hl⟩ := back.transport_order hp
  exact ⟨q,hq,by rw [hl,hlen,Transport.optimum_effective ds h]⟩

theorem gap_of_bounds (upper : LengthUpperBound) (attained : LengthAttained) : YuanGapAtLongest := by
  intro ds hd p hp
  obtain ⟨q,hq,eq⟩ := attained ds hd
  have h₁ := upper ds hd p hp.1
  have h₂ := hp.2 q hq
  unfold optimumFormula at eq h₁
  omega

end Grid.Finish
