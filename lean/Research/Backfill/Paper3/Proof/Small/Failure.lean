import Research.Backfill.Paper3.Proof.Small.Tables

/-!
# The smallest counterexample (`ExactFailureSix`, `SmallestCounterexample`)

At `(n, d) = (6, 3)` we have `i_γ = N_{≤⌊18γ⌋}` (`P3Basic.iGamma_eq_iCount_floor`), every cubic
graph on six vertices is `K_{3,3}` or the prism (`cubicSix`), and by Table 1 the prism has more
sets than `K_{3,3}` exactly at `t = 1` (for `t ≥ 9` every set counts), i.e. for
`γ ∈ [1/18, 1/9)`. The admissible pairs with `n < 6`, and `(6, 1)`, are trivial cases
(hypothesis `TrivialCasesTrue`).
-/

set_option autoImplicit false

namespace P3Small

open Finset SimpleGraph BackfillPaper3.Challenge

theorem iCount_le_two_pow {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) : iCount G t ≤ 2 ^ Fintype.card V := by
  unfold iCount
  calc #((univ : Finset (Finset V)).filter fun A => edgesIn G A ≤ t)
      ≤ #(univ : Finset (Finset V)) := card_filter_le _ _
    _ = 2 ^ Fintype.card V := by rw [card_univ, Fintype.card_finset]

theorem iCount_mono {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (h : s ≤ t) : iCount G s ≤ iCount G t := by
  unfold iCount
  apply card_le_card
  intro A hA
  rw [mem_filter] at hA ⊢
  exact ⟨hA.1, hA.2.trans h⟩

/-- `N_{≤t}(prism) ≤ N_{≤t}(K_{3,3})` for every `t ≠ 1`. -/
theorem prism_le_k33 {t : ℕ} (ht : t ≠ 1) : iCount prism t ≤ iCount (Kdd 3) t := by
  by_cases h10 : t < 10
  · rw [iCount_prism, iCount_K33]
    have h := prism_le_k33_small
    rw [nall_iff] at h
    have h1 := h t h10
    rw [beq_false ht, Bool.false_or, Nat.ble_eq] at h1
    exact h1
  · have hK : iCount (Kdd 3) t = 64 := by
      apply le_antisymm
      · exact (iCount_le_two_pow _ t).trans (by simp)
      · calc 64 = iCount (Kdd 3) 9 := by rw [iCount_K33, nleB_k33_nine]
          _ ≤ iCount (Kdd 3) t := iCount_mono _ (by omega)
    rw [hK]
    exact (iCount_le_two_pow _ t).trans (by simp)

/-- On six vertices with `d = 3`: `i_γ = N_{≤⌊18γ⌋}`. -/
theorem iGamma_six {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hV : Fintype.card V = 6) {γ : ℝ} (hγ : 0 ≤ γ) :
    iGamma G 3 γ = iCount G ⌊γ * 18⌋₊ := by
  rw [P3Basic.iGamma_eq_iCount_floor G 3 hγ, hV,
    show γ * ((3 : ℕ) : ℝ) * ((6 : ℕ) : ℝ) = γ * 18 by push_cast; ring]

/-- At `(n, d) = (6, 3)`, Question 1.3 holds at `γ ≥ 0` iff `⌊18γ⌋ ≠ 1`. -/
theorem careniniQuestion_six_iff {γ : ℝ} (hγ : 0 ≤ γ) :
    CareniniQuestion 6 3 γ ↔ ⌊γ * 18⌋₊ ≠ 1 := by
  have hcardK : Fintype.card (Fin (6 / (2 * 3)) × (Fin 3 ⊕ Fin 3)) = 6 := by simp
  have hK : ∀ t, iCount (KddUnion (6 / (2 * 3)) 3) t = iCount (Kdd 3) t := fun t =>
    (iCount_K13 t).trans (iCount_K33 t).symm
  constructor
  · intro hQ h1
    have h := hQ (Fin 3 × Fin 2) prism (by simp) prism_regular
    rw [iGamma_six prism (by simp) hγ, iGamma_six _ hcardK hγ, hK, h1, iCount_prism,
      iCount_K33, nleB_prism_one, nleB_k33_one] at h
    omega
  · intro h1 V _ _ G _ hV hG
    rw [iGamma_six G hV hγ, iGamma_six _ hcardK hγ, hK]
    rcases cubicSix V G hV hG with h | h
    · obtain ⟨e⟩ := h
      exact (P3Basic.iCount_iso e _).le
    · obtain ⟨e⟩ := h
      exact (P3Basic.iCount_iso e _).le.trans (prism_le_k33 h1)

/-- §1: at `(n, d) = (6, 3)`, `K_{3,3}` fails to be a maximiser exactly for `γ ∈ [1/18, 1/9)`. -/
theorem exactFailureSix : ExactFailureSix := by
  intro γ hγ
  rw [careniniQuestion_six_iff hγ, ne_eq, not_not, Nat.floor_eq_iff (by positivity)]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- §1: `(6, 3, 1/18)` is the smallest counterexample (smallest `n`, then smallest `γ`). -/
theorem smallestCounterexample (hT : TrivialCasesTrue) : SmallestCounterexample := by
  unfold SmallestCounterexample
  refine ⟨(exactFailureSix (1 / 18) (by norm_num)).mpr ⟨le_refl _, by norm_num⟩, ?_, ?_⟩
  · intro n d hadm hn6 γ _
    refine hT n d hadm ?_ γ
    obtain ⟨hd, hn, k, rfl⟩ := hadm
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hn
      · exact h
    have h2 : 2 * d * 1 ≤ 2 * d * k := Nat.mul_le_mul_left (2 * d) hk
    have hd2 : d ≤ 2 := by omega
    interval_cases d
    · exact Or.inl rfl
    · right
      have hk1 : k = 1 := by omega
      subst hk1
      exact ⟨rfl, rfl⟩
  · rintro d ⟨hd, -, hdiv⟩ γ hγ hγ18
    have h6 : 2 * d ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
    have hd3 : d ≤ 3 := by omega
    have hd13 : d = 1 ∨ d = 3 := by
      interval_cases d
      · exact Or.inl rfl
      · exfalso
        revert hdiv
        decide
      · exact Or.inr rfl
    rcases hd13 with rfl | rfl
    · exact hT 6 1 (by unfold Admissible; decide) (Or.inl rfl) γ
    · by_contra hQ
      have h := (exactFailureSix γ hγ).mp hQ
      linarith [h.1]

end P3Small
