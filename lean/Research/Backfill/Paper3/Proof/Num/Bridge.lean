import Research.Backfill.Paper3.Proof.Num.Loop
import Research.Backfill.Paper3.Proof.Tier0
import Research.Backfill.Paper3.Proof.L67.Lemma6

/-!
# From `i_γ` to prefix sums of coefficient lists

`i_γ(G) = N_{≤⌊γdn⌋}(G) = Σ_{s ≤ ⌊γdn⌋} [z^s] P_G` for `γ = p/q`, with
`P_{mK_{d,d}} = P_d^m` and `P_{G_n} = P_{H_d}^{⌊m/2⌋} P_d^{m mod 2}`. The polynomials `P_d` and `W_{αβ}`
are lists computed from their defining double sums (`pdList`, `wList`); `P_{H_d}` is identified
with a given list through Lemma 6 (`P_{2K} − P_H = 2(z − 1)(W₀₀W₁₁ − W₁₀²)`), rearranged so that
both sides have nonnegative coefficients and can be compared as lists. `cmp_of_run` turns a
successful run of the loop of `Research.Backfill.Paper3.Proof.Num.Loop` into comparisons of `i_γ(m K_{d,d})` and `i_γ(G_n)`.
-/

set_option autoImplicit false

namespace P3Num

open Finset Polynomial BackfillPaper3.Challenge

/-! ### Lists for sums of monomials -/

/-- `c X^k` as a list. -/
def monoL (k c : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [c] (fun _ ih => 0 :: ih) k

theorem toPoly_monoL (k c : ℕ) : toPoly (monoL k c) = (c : ℤ[X]) * X ^ k := by
  induction k with
  | zero => simp [monoL]
  | succ k ih =>
    show toPoly (0 :: monoL k c) = _
    rw [toPoly_cons, ih, pow_succ]
    push_cast
    ring

/-- `Σ_{i < n} f i` as a list. -/
def sumRange (n : ℕ) (f : ℕ → List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [] (fun i acc => addL acc (f i)) n

theorem toPoly_sumRange (n : ℕ) (f : ℕ → List ℕ) :
    toPoly (sumRange n f) = ∑ i ∈ range n, toPoly (f i) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    show toPoly (addL (sumRange n f) (f n)) = _
    rw [toPoly_addL, ih, Finset.sum_range_succ]

/-- The coefficient list of `P_d`. -/
def pdList (d : ℕ) : List ℕ :=
  sumRange (d + 1) fun a => sumRange (d + 1) fun b => monoL (a * b) (d.choose a * d.choose b)

/-- The coefficient list of `W_{αβ}`. -/
def wList (d α β : ℕ) : List ℕ :=
  sumRange d fun i => sumRange d fun j =>
    monoL (i * j + α * j + β * i) ((d - 1).choose i * (d - 1).choose j)

theorem Pd_eq_toPoly (d : ℕ) : Pd d = toPoly (pdList d) := by
  rw [pdList, toPoly_sumRange, Pd]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toPoly_sumRange]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [toPoly_monoL, map_natCast]

theorem Wpoly_eq_toPoly (d α β : ℕ) : Wpoly d α β = toPoly (wList d α β) := by
  rw [wList, toPoly_sumRange, Wpoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toPoly_sumRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toPoly_monoL, map_natCast]

/-- Left side of `P_H + 2z W₀₀W₁₁ + 2W₁₀² = P_d² + 2W₀₀W₁₁ + 2z W₁₀²`. -/
def hLhs (d : ℕ) (Hl : List ℕ) : List ℕ :=
  addL (addL Hl (scaleL 2 (0 :: mulL (wList d 0 0) (wList d 1 1))))
    (scaleL 2 (mulL (wList d 1 0) (wList d 1 0)))

/-- Right side of `P_H + 2z W₀₀W₁₁ + 2W₁₀² = P_d² + 2W₀₀W₁₁ + 2z W₁₀²`. -/
def hRhs (d : ℕ) : List ℕ :=
  addL (addL (mulL (pdList d) (pdList d)) (scaleL 2 (mulL (wList d 0 0) (wList d 1 1))))
    (scaleL 2 (0 :: mulL (wList d 1 0) (wList d 1 0)))

/-- `P_{H_d}` is the polynomial of a list `Hl` once the rearranged Lemma 6 identity holds
for `Hl` (any choice of the switched edges). -/
theorem edgePoly_Hd_eq (d : ℕ) (hd : 2 ≤ d) (Hl : List ℕ) (h : hLhs d Hl = hRhs d)
    (a₁ b₁ a₂ b₂ : Fin d) : edgePoly (Hd d a₁ b₁ a₂ b₂) = toPoly Hl := by
  have e1 := P3L67.lemma6_poly d hd a₁ b₁ a₂ b₂
  have e2 : edgePoly (KddUnion 2 d) = toPoly (pdList d) ^ 2 := by
    rw [P3Basic.check_PolyFacts.2.2.1, Pd_eq_toPoly]
  have e3 := congrArg toPoly h
  simp only [hLhs, hRhs, toPoly_addL, toPoly_scaleL, toPoly_mulL, toPoly_cons, Nat.cast_ofNat,
    Nat.cast_zero, zero_add] at e3
  rw [Dpoly, Wpoly_eq_toPoly, Wpoly_eq_toPoly, Wpoly_eq_toPoly] at e1
  linear_combination -e1 + e2 - e3

/-! ### `i_γ` as prefix sums -/

theorem iCount_eq_prefN {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℤ[X]) (hp : edgePoly G = p) (t : ℕ) : iCount G t = prefN p t := by
  have h := P3Basic.iCount_eq_sum_coeff G t
  rw [hp] at h
  rw [prefN, ← h, Int.toNat_natCast]

theorem floor_thr (p q d N : ℕ) : ⌊(p : ℝ) / q * d * N⌋₊ = p * d * N / q := by
  rw [show (p : ℝ) / q * d * N = ((p * d * N : ℕ) : ℝ) / (q : ℕ) by push_cast; ring]
  exact Nat.floor_div_eq_div _ _

theorem iGamma_KddUnion (m d p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) :
    iGamma (KddUnion m d) d γ = prefN (Pd d ^ m) (p * d * (2 * d * m) / q) := by
  have h0 : 0 ≤ γ := by
    rw [hγ]
    positivity
  rw [P3Basic.iGamma_eq_iCount_floor _ d h0, P3Basic.card_KddUnion, hγ, floor_thr]
  exact iCount_eq_prefN _ _ (P3Basic.check_PolyFacts.2.2.1 m d) _

theorem card_GnV (d m : ℕ) : Fintype.card (GnV d m) = 2 * d * m := by
  simp only [GnV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  conv_rhs => rw [← Nat.div_add_mod m 2]
  ring

theorem edgePoly_Gn (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) :
    edgePoly (Gn d m a₁ b₁ a₂ b₂) = edgePoly (Hd d a₁ b₁ a₂ b₂) ^ (m / 2) * Pd d ^ (m % 2) := by
  have h1 : edgePoly (Gn d m a₁ b₁ a₂ b₂) =
      edgePoly (copies (m / 2) (Hd d a₁ b₁ a₂ b₂)) * edgePoly (KddUnion (m % 2) d) :=
    P3Basic.edgePoly_sum _ _
  rw [h1, P3Basic.edgePoly_copies, P3Basic.check_PolyFacts.2.2.1]

theorem iGamma_Gn (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) (p q : ℕ) (γ : ℝ) (hγ : γ = (p : ℝ) / q) :
    iGamma (Gn d m a₁ b₁ a₂ b₂) d γ =
      prefN (edgePoly (Hd d a₁ b₁ a₂ b₂) ^ (m / 2) * Pd d ^ (m % 2)) (p * d * (2 * d * m) / q) := by
  have h0 : 0 ≤ γ := by
    rw [hγ]
    positivity
  rw [P3Basic.iGamma_eq_iCount_floor _ d h0, card_GnV, hγ, floor_thr]
  exact iCount_eq_prefN _ _ (edgePoly_Gn d m a₁ b₁ a₂ b₂) _

/-- A successful run of the loop decides the comparison of `i_γ(m K_{d,d})` and `i_γ(G_n)`
(`γ = p/q`) at every queried `m`. -/
theorem cmp_of_run (d : ℕ) (K H : List ℕ) (hK : Pd d = toPoly K) (a₁ b₁ a₂ b₂ : Fin d)
    (hH : edgePoly (Hd d a₁ b₁ a₂ b₂) = toPoly H) (T : ℕ) (Q : ℕ → List (ℕ × ℕ)) (M : ℕ)
    (hrun : (runSt K H T Q M).ok = true) (m : ℕ) (hm1 : 1 ≤ m) (hmM : m ≤ M) (p q : ℕ) (γ : ℝ)
    (hγ : γ = (p : ℝ) / q) (c : ℕ) (hq : (p * d * (2 * d * m) / q, c) ∈ Q m)
    (hT : p * d * (2 * d * m) / q < T) :
    cmpN (iGamma (KddUnion m d) d γ) (iGamma (Gn d m a₁ b₁ a₂ b₂) d γ) = c := by
  rw [iGamma_KddUnion m d p q γ hγ, iGamma_Gn d m a₁ b₁ a₂ b₂ p q γ hγ, hK, hH]
  exact (runSt_spec K H T Q M).2.2 hrun m hm1 hmM _ hq hT

end P3Num
