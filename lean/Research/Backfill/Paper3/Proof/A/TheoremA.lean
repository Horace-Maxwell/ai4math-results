import Research.Backfill.Paper3.Proof.A.TwoRegular

/-!
# Paper 3, Theorem A and the maximisers at `γ*`

At `γ* = t*/(dn)` one has `γ* d n = t*`, so `i_{γ*} = N_{≤t*}` (for `n > 0`), and by
Proposition 2 `N_{≤t*}(G) - N_{≤t*}(G') = (2T(G) - Q(G)) - (2T(G') - Q(G'))` for `d`-regular `G`,
`G'` on `n` vertices. With `T(m K_{d,d}) = 0`, Lemma 3 gives part (a); for `d = 2`,
`Q(m C₄) = m` and `4 Q(G) < n` unless `G ≅ m K_{2,2}` give part (b).
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

/-- For `n = 2dm`, `dn/2 = d²m`. -/
theorem half_d_mul (d m : ℕ) : d * (2 * d * m) / 2 = d * d * m := by
  rw [show d * (2 * d * m) = 2 * (d * d * m) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem tStar_eq (d m : ℕ) : tStar (2 * d * m) d = (d : ℤ) * d * m - 3 * d + 1 := by
  unfold tStar
  rw [half_d_mul]
  push_cast
  ring

/-- `γ* d n = t*` for `n, d > 0`. -/
theorem gammaStar_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    gammaStar n d * d * (n : ℝ) = (tStar n d : ℝ) := by
  unfold gammaStar
  have : (d : ℝ) * n ≠ 0 := by positivity
  field_simp

/-- `i_{γ*} = N_{≤t*}` on `n > 0` vertices. -/
theorem iGamma_gammaStar {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n d : ℕ} (hV : Fintype.card V = n) (hn : 0 < n) (hd : 0 < d) :
    iGamma G d (gammaStar n d) = NleZ G (tStar n d) :=
  iGamma_eq_NleZ G d _ (by rw [hV]; exact gammaStar_mul hn hd)

theorem card_kddUnion' (d m : ℕ) : Fintype.card (Fin m × (Fin d ⊕ Fin d)) = 2 * d * m := by
  rw [card_kddUnion]
  ring

/-- Proposition 2 for `m K_{d,d}` (`n = 2dm`): `T = 0`. -/
theorem NleZ_kddUnion {d m : ℕ} (hd : 2 ≤ d) :
    (NleZ (KddUnion m d) (tStar (2 * d * m) d) : ℤ) =
      2 ^ (2 * d * m) - 1 - (2 * d * m : ℕ) - ((2 * d * m).choose 2 : ℕ) -
        (2 * d * m : ℕ) * (d.choose 2 : ℕ) - Qcount (KddUnion m d) d := by
  have p := proposition2 _ (KddUnion m d) d hd (isRegularOfDegree_of_inst (kddUnion_regular m d))
  rw [card_kddUnion', triangles_eq_zero (kddUnion_cliqueFree m d)] at p
  rw [p]
  push_cast
  ring

/-- **Theorem A.** -/
theorem theoremA : TheoremA := by
  intro n d hd hn hdn hne
  obtain ⟨m, rfl⟩ := hdn
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hn
    · exact h
  have hd0 : 0 < d := by omega
  have hmdiv : 2 * d * m / (2 * d) = m := Nat.mul_div_cancel_left m (by omega)
  have hm2 : d = 2 → 2 ≤ m := by
    rintro rfl
    by_contra h
    have h1 : m = 1 := by omega
    subst h1
    exact hne rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tStar_eq]
    rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | h3
    · have := hm2 rfl
      push_cast
      nlinarith
    · have h1 : (d : ℤ) * d * m ≥ d * d := by
        have : (1 : ℤ) ≤ m := by exact_mod_cast hm
        have : (0 : ℤ) ≤ d * d := by positivity
        nlinarith
      have h2 : (3 : ℤ) ≤ d := by exact_mod_cast h3
      nlinarith
  · unfold gammaStar
    rw [tStar_eq]
    have hdR : (d : ℝ) ≠ 0 := by positivity
    have hmR : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      exact this.ne'
    push_cast
    field_simp
    ring
  · intro hd3 V _ _ G _ hV hG
    rw [hmdiv]
    have hpos : 0 < 2 * d * m := by positivity
    rw [iGamma_gammaStar G hV hpos hd0,
      iGamma_gammaStar (KddUnion m d) (card_kddUnion' d m) hpos hd0]
    have p1 := proposition2 V G d (by omega) hG
    rw [hV] at p1
    have p2 := NleZ_kddUnion (m := m) (show 2 ≤ d by omega)
    have hQ0 : Qcount (KddUnion m d) d = 0 := by
      have := five_mul_Qcount_le_of_three_le (KddUnion m d) hd3
        (isRegularOfDegree_of_inst (kddUnion_regular m d))
      rw [triangles_eq_zero (kddUnion_cliqueFree m d)] at this
      omega
    have hQG := five_mul_Qcount_le_of_three_le G hd3 hG
    have hdiff : (NleZ G (tStar (2 * d * m) d) : ℤ) - NleZ (KddUnion m d) (tStar (2 * d * m) d) =
        2 * (triangles G : ℤ) - Qcount G d := by
      rw [p1, p2, hQ0]
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · have hdiffR : ((NleZ G (tStar (2 * d * m) d) : ℕ) : ℝ) -
          ((NleZ (KddUnion m d) (tStar (2 * d * m) d) : ℕ) : ℝ) =
            2 * (triangles G : ℝ) - Qcount G d := by
        exact_mod_cast hdiff
      rw [hdiffR]
      have hQGR : 5 * (Qcount G d : ℝ) ≤ 3 * triangles G := by exact_mod_cast hQG
      linarith
    · constructor
      · intro heq
        rw [← triangles_eq_zero_iff]
        have h0 : 2 * (triangles G : ℤ) - Qcount G d = 0 := by
          rw [← hdiff, heq]
          ring
        omega
      · intro hcf
        have hT : triangles G = 0 := triangles_eq_zero hcf
        have hQ : Qcount G d = 0 := by
          rw [hT] at hQG
          omega
        have : (NleZ G (tStar (2 * d * m) d) : ℤ) = NleZ (KddUnion m d) (tStar (2 * d * m) d) := by
          rw [hT, hQ] at hdiff
          omega
        exact_mod_cast this
  · intro hd2 V _ _ G _ hV hG hiso
    subst hd2
    have hm2' := hm2 rfl
    have hm4 : 2 * 2 * m / 4 = m := by omega
    rw [hm4] at hiso ⊢
    have hpos : 0 < 2 * 2 * m := by positivity
    rw [iGamma_gammaStar G hV hpos (by norm_num),
      iGamma_gammaStar (KddUnion m 2) (card_kddUnion' 2 m) hpos (by norm_num)]
    have p1 := proposition2 V G 2 le_rfl hG
    rw [hV] at p1
    have p2 := NleZ_kddUnion (d := 2) (m := m) le_rfl
    have hQK : Qcount (KddUnion m 2) 2 = m := by
      rw [Qcount_two _ (isRegularOfDegree_of_inst (kddUnion_regular m 2)), card_heavy4_kddUnion]
    have hQG : 4 * Qcount G 2 < Fintype.card V := four_mul_Qcount_lt G hG (by rw [hV, hm4]; exact hiso)
    rw [hV] at hQG
    have hQG' : 4 * (Qcount G 2 : ℤ) < 2 * 2 * m := by exact_mod_cast hQG
    have hT : (0 : ℤ) ≤ triangles G := by positivity
    have : (NleZ (KddUnion m 2) (tStar (2 * 2 * m) 2) : ℤ) < NleZ G (tStar (2 * 2 * m) 2) := by
      rw [p1, p2, hQK]
      linarith
    exact_mod_cast this

/-- §10, question 4: at `γ*`, `i_{γ*}(G) ≤ i_{γ*}(H)` iff `2T(G) - Q(G) ≤ 2T(H) - Q(H)`. -/
theorem maximisersAtGammaStar : MaximisersAtGammaStar := by
  intro n d hd V W _ _ _ _ G H _ _ hV hW hG hH
  have p1 := proposition2 V G d hd hG
  have p2 := proposition2 W H d hd hH
  rw [hV] at p1
  rw [hW] at p2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hVe : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    have hWe : IsEmpty W := Fintype.card_eq_zero_iff.1 hW
    let φ : G ≃g H := ⟨Equiv.equivOfIsEmpty V W, fun {a} => isEmptyElim a⟩
    have h1 := iGamma_iso_all φ d (gammaStar 0 d)
    have h2 := NleZ_iso φ (tStar 0 d)
    rw [h2] at p1
    rw [h1]
    constructor
    · intro _
      linarith
    · intro _
      exact le_rfl
  · rw [iGamma_gammaStar G hV hn (by omega), iGamma_gammaStar H hW hn (by omega)]
    constructor
    · intro h
      have h' : (NleZ G (tStar n d) : ℤ) ≤ NleZ H (tStar n d) := by exact_mod_cast h
      rw [p1, p2] at h'
      linarith
    · intro h
      have h' : (NleZ G (tStar n d) : ℤ) ≤ NleZ H (tStar n d) := by
        rw [p1, p2]
        linarith
      exact_mod_cast h'

end P3A
