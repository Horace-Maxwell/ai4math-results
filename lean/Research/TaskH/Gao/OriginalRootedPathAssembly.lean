import Research.TaskH.Gao.OriginalNormalizedAssembly
import Research.TaskH.Gao.RootEdgeAdmissiblePreprocessing
import Research.TaskH.Fan.FanTwoPathProof

/-! Complete candidate assembly of the original positive-k rooted theorem.
The strict-cardinality IH is internal to strong induction over all positive
counts. The endpoint has only original rooted connectivity and degree inputs. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem admissible_two_of_two_path_witness
    (G : SimpleGraph V) (x y : V) (h : HasTwoPaths G x y) :
    HasAdmissiblePaths G x y 2 := by
  obtain ⟨p, q, hp, hq, hp2, _hq2, hgap⟩ := h
  obtain ⟨d, hd, hlen⟩ : ∃ d : ℕ, (d = 1 ∨ d = 2) ∧
      q.length = p.length + d := by
    rcases hgap with hgap | hgap
    · exact ⟨1, Or.inl rfl, hgap.symm⟩
    · exact ⟨2, Or.inr rfl, hgap.symm⟩
  let f : Fin 2 → G.Walk x y := Fin.cases p (fun _ : Fin 1 => q)
  refine ⟨p.length, d, f, hp2, hd, ?_⟩
  intro i
  fin_cases i
  · change p.IsPath ∧ p.length = p.length + 0 * d
    exact ⟨hp, by omega⟩
  · change q.IsPath ∧ q.length = p.length + 1 * d
    exact ⟨hq, by omega⟩

theorem rooted_admissible_from_smaller_IH [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hroot : RootedTwoConnected G x y) (hk : 1 ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  by_cases hk1 : k = 1
  · subst k
    exact rooted_has_admissible_one hroot
  · by_cases hk2 : k = 2
    · subst k
      exact admissible_two_of_two_path_witness G x y
        (fan_rooted_two_paths G x y hroot hd)
    · have hk3 : 3 ≤ k := by omega
      by_contra hno
      obtain ⟨hnoedge, _hr, hdegree, hcounter, hordinary⟩ :=
        normalized_counterexample_preprocessing G x y k hroot hk hd ih hno
      exact hcounter (ordinary_normalized_admissible_from_smaller_IH
        (rootEdgeDeleted G x y) x y k hordinary hroot.1 hnoedge hk3 hdegree ih)

theorem gao_original_rooted_path_claim : RootedPathClaim.{u} := by
  have hmain : ∀ n : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (G : SimpleGraph W) (x y : W) (k : ℕ), 1 ≤ k →
      RootedTwoConnected G x y → NonrootDegreeAtLeast G x y (k + 1) →
      HasAdmissiblePaths G x y k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst hcard G x y k hk hroot hdeg
      apply rooted_admissible_from_smaller_IH G x y k hroot hk hdeg
      intro U instU J a b r hlt hr hrootJ hdegJ
      have hlt' : Fintype.card U < n := by simpa only [hcard] using hlt
      exact ih (Fintype.card U) hlt' U rfl J a b r hr hrootJ hdegJ
  intro k hk W inst G x y hroot hdeg
  exact hmain (Fintype.card W) W rfl G x y k hk hroot hdeg

theorem gao_original_rooted_admissible_paths [Fintype V]
    (G : SimpleGraph V) (x y : V) (k : ℕ) (hk : 1 ≤ k)
    (hroot : RootedTwoConnected G x y)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1)) :
    HasAdmissiblePaths G x y k := by
  exact gao_original_rooted_path_claim k hk V G x y hroot hdeg

#print axioms admissible_two_of_two_path_witness
#print axioms rooted_admissible_from_smaller_IH
#print axioms gao_original_rooted_path_claim
#print axioms gao_original_rooted_admissible_paths
end TaskH.Gao
