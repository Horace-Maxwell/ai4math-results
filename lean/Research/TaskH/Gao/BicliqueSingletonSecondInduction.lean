import Research.TaskH.Gao.BicliqueSingletonSecondGeometry
import Research.TaskH.Gao.Challenge

/-! The actual |C|+2 quotient is strictly smaller before the rooted IH call. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_second_family_from_smaller_IH [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k eps : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (heps : (eps = 0 ∧ s + 2 ≤ A.ncard) ∨ (eps = 1 ∧ A.ncard = s + 1))
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoB : ¬∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1)
    (hu : u ∈ singletonG1Boundary G (bicliqueSingletonCore A B y) C)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths
      (boundaryQuotient G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u
        (by rw [singleton_g1_full_boundary]; exact hu))) (k - s + eps) := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let : Fintype (IdentificationVertex (boundaryCollapse G R u)) := singletonG1Fintype G K C u
  have hK := biclique_first_core_card A B y s hy hs hB
  change 3 ≤ K.ncard at hK
  have hroot := singleton_g1_rooted G K C x u hG (Or.inl (Or.inr hx)) (by omega) hu
  have hdegree := biclique_second_nonroot_degree G A B x y u s k eps C hx hs (by omega)
    heps hNx hNy hnoB hu hcap hd
  have hn := biclique_first_strict_order G A B y u s C hy hs hB hu
  change Nat.card (IdentificationVertex (boundaryCollapse G R u)) < Nat.card V at hn
  have hn' : Fintype.card (IdentificationVertex (boundaryCollapse G R u)) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hn
  have hdegree' : NonrootDegreeAtLeast (boundaryQuotient G R u) none
      (some (boundaryRetainedRoot G R u (by rw [singleton_g1_full_boundary]; exact hu)))
      (k - s + eps + 1) := by
    have he : k - s + eps + 1 = k - s + 1 + eps := by omega
    rw [he]
    exact hdegree
  exact ih (IdentificationVertex (boundaryCollapse G R u)) (boundaryQuotient G R u) none
    (some (boundaryRetainedRoot G R u (by rw [singleton_g1_full_boundary]; exact hu)))
    (k - s + eps) hn' (by omega) hroot hdegree'

#print axioms biclique_second_family_from_smaller_IH
end TaskH.Gao
