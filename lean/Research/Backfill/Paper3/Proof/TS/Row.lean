import Research.Backfill.Paper3.Proof.TS.Classify
import Research.Backfill.Paper3.Proof.Basic

/-!
# One row of Table 2 from certified data

`table2Row_of_data`: a list `R` of `d`-regular graphs on `Fin (2d)`, closed under 2-switches
(canonical form), pairwise non-isomorphic, with `K_{d,d} ≅ R i₀` and `N_{≤t}(R i) = P i t`,
gives `Table2Row d k fails uniq` as soon as the finite conditions on the numbers `P i t` hold.
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

theorem card_nbr_eq_degree' {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (i : Fintype (G.neighborSet v)) : (nbr G v).card = @SimpleGraph.degree V G v i := by
  rw [← @SimpleGraph.card_neighborFinset_eq_degree V G v i]
  congr 1
  ext t
  rw [mem_nbr, @SimpleGraph.mem_neighborFinset V G v i]

section Row

variable {d k : ℕ}

/-- A `d`-regular graph on `Fin (2d)` is isomorphic to some `R i` and has its `N_{≤t}`. -/
theorem class_of_regular (R : Fin k → SimpleGraph (Fin (2 * d))) (i₀ : Fin k)
    (P : Fin k → ℕ → ℕ) (hdeg : ∀ i (v : Fin (2 * d)), (nbr (R i) v).card = d)
    (hclosed : ∀ i (u₁ w₁ u₂ w₂ : Fin (2 * d)), u₁ < w₁ → u₁ < u₂ → u₁ < w₂ →
      IsSwitch (R i) u₁ w₁ u₂ w₂ → ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j))
    (hP : ∀ i, ∀ t ≤ d ^ 2, ∀ (_ : DecidableRel (R i).Adj), iCount (R i) t = P i t)
    (G : SimpleGraph (Fin (2 * d))) (hG : ∀ v, (nbr G v).card = d) :
    ∃ i, Nonempty (G ≃g R i) ∧ ∀ (_ : DecidableRel G.Adj), ∀ t ≤ d ^ 2, iCount G t = P i t := by
  classical
  obtain ⟨i, ⟨φ⟩⟩ := classify R hclosed i₀ G (fun v => (hdeg i₀ v).trans (hG v).symm)
  exact ⟨i, ⟨φ⟩, fun _ t ht => (P3Basic.iCount_iso φ t).trans (hP i t ht _)⟩

theorem nbr_of_regular (G : SimpleGraph (Fin (2 * d))) [SimpleGraph.LocallyFinite G]
    (hG : G.IsRegularOfDegree d) (v : Fin (2 * d)) : (nbr G v).card = d :=
  (card_nbr_eq_degree' G v _).trans (hG v)

theorem exists_getD_ne {L₁ L₂ : List ℕ} {m : ℕ} (h : L₁ ≠ L₂) (h₁ : L₁.length = m)
    (h₂ : L₂.length = m) : ∃ t < m, L₁.getD t 0 ≠ L₂.getD t 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply List.ext_getElem (h₁.trans h₂.symm)
  intro t ht1 ht2
  have := hc t (h₁ ▸ ht1)
  rwa [List.getD_eq_getElem _ _ ht1, List.getD_eq_getElem _ _ ht2] at this

/-- Non-isomorphism from the `N_{≤t}` profiles, except for listed pairs handled separately. -/
theorem noniso_of_prof (R : Fin k → SimpleGraph (Fin (2 * d))) (P : Fin k → ℕ → ℕ)
    (hP : ∀ i, ∀ t ≤ d ^ 2, ∀ (_ : DecidableRel (R i).Adj), iCount (R i) t = P i t)
    (special : Fin k → Fin k → Prop) (hspec : ∀ i j, special i j → IsEmpty (R i ≃g R j))
    (hsep : ∀ i j, i ≠ j → (∃ t ≤ d ^ 2, P i t ≠ P j t) ∨ special i j) :
    ∀ i j, Nonempty (R i ≃g R j) → i = j := by
  classical
  intro i j ⟨φ⟩
  by_contra hij
  rcases hsep i j hij with ⟨t, ht, hne⟩ | hs
  · exact hne ((hP i t ht _).symm.trans ((P3Basic.iCount_iso φ t).trans (hP j t ht _)))
  · exact (hspec i j hs).false φ

theorem table2Row_of_data {fails : List (ℕ × ℕ × ℕ)} {uniq : List ℕ}
    (R : Fin k → SimpleGraph (Fin (2 * d))) (i₀ : Fin k) (P : Fin k → ℕ → ℕ)
    (hdeg : ∀ i (v : Fin (2 * d)), (nbr (R i) v).card = d)
    (hnoniso : ∀ i j, Nonempty (R i ≃g R j) → i = j)
    (hclosed : ∀ i (u₁ w₁ u₂ w₂ : Fin (2 * d)), u₁ < w₁ → u₁ < u₂ → u₁ < w₂ →
      IsSwitch (R i) u₁ w₁ u₂ w₂ → ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j))
    (hP : ∀ i, ∀ t ≤ d ^ 2, ∀ (_ : DecidableRel (R i).Adj), iCount (R i) t = P i t)
    (hK : Nonempty (Kdd d ≃g R i₀))
    (hfle : ∀ r ∈ fails, r.1 ≤ d ^ 2) (hule : ∀ t ∈ uniq, t ≤ d ^ 2)
    (hfails : ∀ t ≤ d ^ 2, (∃ i, P i₀ t < P i t) ↔ t ∈ fails.map Prod.fst)
    (hmax : ∀ r ∈ fails, ((∃ i, P i r.1 = r.2.1) ∧ ∀ i, P i r.1 ≤ r.2.1) ∧ P i₀ r.1 = r.2.2)
    (huniq : ∀ t ∈ uniq, ∀ i, i ≠ i₀ → P i t < P i₀ t)
    (htie : ∀ t ≤ d ^ 2, t ∉ fails.map Prod.fst → t ∉ uniq →
      (∀ i, P i t ≤ P i₀ t) ∧ ∃ i, i ≠ i₀ ∧ P i t = P i₀ t) :
    Table2Row d k fails uniq := by
  classical
  obtain ⟨φK⟩ := hK
  have hKt : ∀ t ≤ d ^ 2, iCount (Kdd d) t = P i₀ t :=
    fun t ht => (P3Basic.iCount_iso φK t).trans (hP i₀ t ht _)
  have hreg : ∀ i, ∀ (_ : SimpleGraph.LocallyFinite (R i)), (R i).IsRegularOfDegree d :=
    fun i _ v => (card_nbr_eq_degree' (R i) v _).symm.trans (hdeg i v)
  have hcls := class_of_regular R i₀ P hdeg hclosed hP
  have hnotK : ∀ i, i ≠ i₀ → IsEmpty (R i ≃g Kdd d) := fun i hi =>
    ⟨fun ψ => hi (hnoniso i i₀ ⟨ψ.trans φK⟩)⟩
  refine ⟨⟨R, fun i => hreg i _, hnoniso, fun G hG => ?_⟩, fun t ht => ?_, fun r hr => ?_,
    fun t ht G hG hGK => ?_, fun t ht hf hu => ?_⟩
  · obtain ⟨i, hi, -⟩ := hcls G (nbr_of_regular G hG)
    exact ⟨i, hi⟩
  · rw [← hfails t ht]
    constructor
    · rintro ⟨G, hG, hlt⟩
      obtain ⟨i, -, hi⟩ := hcls G (nbr_of_regular G hG)
      exact ⟨i, by rw [← hKt t ht, ← hi _ t ht]; exact hlt⟩
    · rintro ⟨i, hi⟩
      exact ⟨R i, hreg i _, by rw [hKt t ht, hP i t ht _]; exact hi⟩
  · have hr1 := hfle r hr
    obtain ⟨⟨⟨i, hi⟩, hle⟩, hK0⟩ := hmax r hr
    refine ⟨⟨⟨R i, hreg i _, by rw [hP i _ hr1 _]; exact hi⟩, fun G hG => ?_⟩,
      by rw [hKt _ hr1]; exact hK0⟩
    obtain ⟨j, -, hj⟩ := hcls G (nbr_of_regular G hG)
    rw [hj _ r.1 hr1]
    exact hle j
  · have ht' := hule t ht
    obtain ⟨i, ⟨φ⟩, hi⟩ := hcls G (nbr_of_regular G hG)
    rw [hi _ t ht', hKt t ht']
    by_cases h : i = i₀
    · subst h
      exact (hGK.false (φ.trans φK.symm)).elim
    · exact huniq t ht i h
  · obtain ⟨hle, i, hi0, heq⟩ := htie t ht hf hu
    refine ⟨fun G hG => ?_, R i, hreg i _, hnotK i hi0, by rw [hP i t ht _, hKt t ht]; exact heq⟩
    obtain ⟨j, -, hj⟩ := hcls G (nbr_of_regular G hG)
    rw [hj _ t ht, hKt t ht]
    exact hle j

end Row

end P3TS
