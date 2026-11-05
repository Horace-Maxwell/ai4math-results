import Research.Backfill.Paper7.IntroThreeLeafFourCycleNeighborSum

/-! Actual finite-neighbor Perron transport with explicit cycle-neighborhood
and external-star premises. A2 topology and the final contradiction remain separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeFourAlternatives
open SimpleGraph Matrix

theorem cycle_neighbor_external_perron_row
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (S : Set V) (u c j : V) (hcj : c ≠ j)
    (huc : G.Adj u c) (huj : G.Adj u j)
    (hcomplete : ∀ x, x ∈ S → (G.Adj u x ↔ x = c ∨ x = j))
    (hfc : f c = 6)
    (hout : ∀ x, x ∉ S → G.Adj x u → f x = 3) :
    3 * f u = 6 + f j + 3 * ((((G.neighborFinset u).erase c).erase j).card : ℝ) := by
  let N := G.neighborFinset u
  have hcN : c ∈ N := (G.mem_neighborFinset u c).mpr huc
  have hjN : j ∈ N := (G.mem_neighborFinset u j).mpr huj
  have hjNc : j ∈ N.erase c := Finset.mem_erase.mpr ⟨hcj.symm, hjN⟩
  let E := (N.erase c).erase j
  have hweights : ∀ x ∈ E, f x = 3 := by
    intro x hx
    obtain ⟨hxj, hxcN⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxc, hxN⟩ := Finset.mem_erase.mp hxcN
    have hxout : x ∉ S := by
      intro hxS
      rcases (hcomplete x hxS).mp ((G.mem_neighborFinset u x).mp hxN) with he | he
      · exact hxc he
      · exact hxj he
    exact hout x hxout ((G.mem_neighborFinset u x).mp hxN).symm
  have hEsum : (∑ x ∈ E, f x) = (E.card : ℝ) * 3 := by
    calc
      (∑ x ∈ E, f x) = ∑ _x ∈ E, (3 : ℝ) :=
        Finset.sum_congr rfl (fun x hx => hweights x hx)
      _ = _ := by simp
  have h1 := Finset.sum_erase_add N f hcN
  have h2 := Finset.sum_erase_add (N.erase c) f hjNc
  have hrow : (∑ x ∈ N, f x) = 3 * f u := by
    simpa only [N, G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
      using congrFun hAf u
  change (∑ x ∈ (N.erase c).erase j, f x) =
    (((N.erase c).erase j).card : ℝ) * 3 at hEsum
  change 3 * f u = 6 + f j + 3 * (((N.erase c).erase j).card : ℝ)
  linarith only [h1, h2, hrow, hEsum, hfc]
#print axioms Paper7IntroThreeFourAlternatives.cycle_neighbor_external_perron_row

theorem cycle_neighbor_weight_alternatives
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (S : Set V) (u c j : V) (hcj : c ≠ j)
    (huc : G.Adj u c) (huj : G.Adj u j)
    (hcomplete : ∀ x, x ∈ S → (G.Adj u x ↔ x = c ∨ x = j))
    (hfc : f c = 6)
    (hout : ∀ x, x ∉ S → G.Adj x u →
      f x = 3 ∧ (f u = 9 ∨ f u = 8 ∨ f u = 6)) :
    (f j = 3 → (f u = 3 ∨ f u = 6 ∨ f u = 8 ∨ f u = 9)) ∧
    (f j = 6 → (f u = 4 ∨ f u = 6 ∨ f u = 8 ∨ f u = 9)) := by
  let E := ((G.neighborFinset u).erase c).erase j
  have hrow := cycle_neighbor_external_perron_row G f hAf S u c j hcj
    huc huj hcomplete hfc (fun x hx hxu => (hout x hx hxu).1)
  by_cases hE : E = ∅
  · have hEc : ((((G.neighborFinset u).erase c).erase j).card : ℝ) = 0 := by
      change (E.card : ℝ) = 0
      simp [hE]
    constructor
    · intro hj
      exact Or.inl (by linarith only [hrow, hEc, hj])
    · intro hj
      exact Or.inl (by linarith only [hrow, hEc, hj])
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hE
    obtain ⟨hxj, hxcN⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxc, hxN⟩ := Finset.mem_erase.mp hxcN
    have hxout : x ∉ S := by
      intro hxS
      rcases (hcomplete x hxS).mp ((G.mem_neighborFinset u x).mp hxN) with he | he
      · exact hxc he
      · exact hxj he
    have hset := (hout x hxout ((G.mem_neighborFinset u x).mp hxN).symm).2
    constructor
    · intro _hj
      rcases hset with h9 | h8 | h6
      · exact Or.inr (Or.inr (Or.inr h9))
      · exact Or.inr (Or.inr (Or.inl h8))
      · exact Or.inr (Or.inl h6)
    · intro _hj
      rcases hset with h9 | h8 | h6
      · exact Or.inr (Or.inr (Or.inr h9))
      · exact Or.inr (Or.inr (Or.inl h8))
      · exact Or.inr (Or.inl h6)
#print axioms Paper7IntroThreeFourAlternatives.cycle_neighbor_weight_alternatives

end Paper7IntroThreeFourAlternatives
