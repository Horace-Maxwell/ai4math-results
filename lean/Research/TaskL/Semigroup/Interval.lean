import Research.TaskL.Semigroup.Algebra
import Research.TaskL.Semigroup.Terminal
import Research.TaskL.Semigroup.CoverStep

namespace TaskL.Semigroup
open Challenge
noncomputable section

variable {S : AddSubmonoid ℕ} {D : Finset (AddSubmonoid ℕ)}

private theorem component_ne_top (hS : Numerical S) (hd : Decomposition S D)
    {Q : AddSubmonoid ℕ} (hQ : Q ∈ D) : Q ≠ ⊤ := by
  obtain ⟨g, _, hg, _⟩ := private_gap hS hd hQ
  intro he
  exact hg (he ▸ show g ∈ (⊤ : AddSubmonoid ℕ) from trivial)

private theorem terminal_or_step (hS : Numerical S) (hd : Decomposition S D) :
    D.card = ((specials S).filter (fun g => frob S < 2*g)).card ∨
    ∃ E, Decomposition S E ∧ score E < score D ∧
      D.card ≤ E.card+1 ∧ E.card ≤ D.card+1 := by
  classical
  have hel := ((decomp_iff hS).mp hd).1
  by_cases hstd : ∀ Q ∈ D, Standard S Q
  · exact Or.inl (terminal_card hS hd (fun Q hQ _ hg =>
      standard_edge (hel Q hQ).1 (hel Q hQ).2 (component_ne_top hS hd hQ) (hstd Q hQ) hg))
  · push Not at hstd
    obtain ⟨Q,hQ,hn⟩ := hstd
    obtain ⟨u,v,P,_,hv,hlt,hP,hSP,hw,hswap⟩ :=
      exchange_of_nonstandard (hel Q hQ).1 (hel Q hQ).2 (component_ne_top hS hd hQ) hn
    obtain ⟨R,hR,hQR,hvR,_,hwR⟩ := repair_component (hel Q hQ).1 hv hlt
    exact Or.inr (rebalance hS hd hQ ⟨hP,hSP⟩ hw hswap ⟨R,hR,hQR,hvR,hwR⟩)

/-- At an omitted length, every decomposition lies on the same side as the common terminal length. -/
private theorem side_of_missing (hS : Numerical S) {j : ℕ} (hj : ¬ HasLength S j)
    (hd : Decomposition S D) :
    D.card < j ↔ ((specials S).filter (fun g => frob S < 2*g)).card < j := by
  have noeq {E : Finset (AddSubmonoid ℕ)} (he : Decomposition S E) : E.card ≠ j :=
    fun h => hj ⟨E,he,h⟩
  have side : ∀ k : ℕ, ∀ E : Finset (AddSubmonoid ℕ),
      score E = k → Decomposition S E →
      (E.card < j ↔ ((specials S).filter (fun g => frob S < 2*g)).card < j) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro E hk he
      rcases terminal_or_step hS he with hstop | ⟨E',he',hlt,hleft,hright⟩
      · rw [hstop]
      · have hside := ih (score E') (hk ▸ hlt) E' rfl he'
        have hgap := noeq he
        have hgap' := noeq he'
        omega
  exact side (score D) D rfl hd

theorem lengthsInterval : Challenge.LengthsInterval := by
  intro S hS a b j ha hb haj hjb
  by_contra hj
  obtain ⟨A,hA,rfl⟩ := ha
  obtain ⟨B,hB,rfl⟩ := hb
  have hlt : A.card < j := lt_of_le_of_ne haj (fun he => hj ⟨A,hA,he⟩)
  have hterminal := (side_of_missing hS hj hA).1 hlt
  have hbad := (side_of_missing hS hj hB).2 hterminal
  omega

end
end TaskL.Semigroup
