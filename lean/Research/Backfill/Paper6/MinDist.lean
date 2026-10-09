import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.Lem22

/-!
# Paper 6 V3: exact minimum distance of the binary Reed–Muller codes

For every r <= m, this source proves both the lower bound for all nonzero
codewords and existence of a genuine polynomial-defined codeword attaining
2^(m-r). The lower bound is by induction on m using the complete binary
half-decomposition. The witness starts with the constant-one polynomial and
successively adds variables by multiplying by the new last coordinate.

Both m = 0 and r = 0 are retained. No multilinearity assumption or extra
nonemptiness assumption is imposed on the frozen target.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Source candidate only; compilation and acceptance are controlled by the root.
-/

set_option autoImplicit false

namespace Paper6MinDistance

open BackfillPaper6.V3

/-- Zero is represented by the zero polynomial at every order. -/
theorem zero_mem_RM (r m : ℕ) : (0 : BFun m) ∈ RM r m := by
  refine ⟨0, by simp, ?_⟩
  funext x
  change (0 : ZMod 2) = MvPolynomial.eval x 0
  rw [map_zero]

/-- The constant-one function is represented by the constant-one polynomial at every order. -/
theorem one_mem_RM (r m : ℕ) : (1 : BFun m) ∈ RM r m := by
  refine ⟨1, by simp, ?_⟩
  funext x
  change (1 : ZMod 2) = MvPolynomial.eval x 1
  rw [map_one]

/-- The all-one word has weight 2^m, including weight one in dimension zero. -/
theorem hammingNorm_one (m : ℕ) : hammingNorm (1 : BFun m) = 2 ^ m := by
  classical
  change (Finset.univ.filter (fun _ : Pt m => (1 : ZMod 2) ≠ 0)).card = 2 ^ m
  have hfilter : Finset.univ.filter (fun _ : Pt m => (1 : ZMod 2) ≠ 0) =
      Finset.univ := Finset.filter_eq_self.mpr (fun _ _ => one_ne_zero)
  rw [hfilter, Finset.card_univ]
  change Fintype.card (Fin m → ZMod 2) = 2 ^ m
  rw [Fintype.card_pi_const, ZMod.card]

/-- A degree-zero binary polynomial represents either the zero or the one function. -/
theorem rm_zero_order_eq_zero_or_one (m : ℕ) (f : BFun m) (hf : f ∈ RM 0 m) :
    f = 0 ∨ f = 1 := by
  rcases hf with ⟨p, hp, rfl⟩
  have hdegree : p.totalDegree = 0 := Nat.eq_zero_of_le_zero hp
  have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbit (p.coeff 0) with hzero | hone
  · left
    funext x
    change MvPolynomial.eval x p = 0
    rw [hpC, MvPolynomial.eval_C, hzero]
  · right
    funext x
    change MvPolynomial.eval x p = 1
    rw [hpC, MvPolynomial.eval_C, hone]

/-- The nonzero word of order zero has full weight. -/
theorem zero_order_weight (m : ℕ) (f : BFun m)
    (hf : f ∈ RM 0 m) (hne : f ≠ 0) : hammingNorm f = 2 ^ m := by
  have hone := (rm_zero_order_eq_zero_or_one m f hf).resolve_left hne
  rw [hone, hammingNorm_one]

/-- If both slices vanish, reconstruction shows that the whole function vanishes. -/
theorem eq_zero_of_halves_zero (m : ℕ) (f : BFun (m + 1))
    (hzero : half0 f = 0) (hone : half1 f = 0) : f = 0 := by
  funext y
  have hy := Paper6HalfDecomposition.reconstruct m f y
  rw [hzero, hone] at hy
  simpa only [Pi.zero_apply, zero_add, mul_zero] using hy

/-- The full nonzero lower bound, for every admissible order and dimension. -/
theorem nonzero_weight_lower_bound (m : ℕ) :
    ∀ r : ℕ, r ≤ m → ∀ f ∈ RM r m, f ≠ 0 →
      2 ^ (m - r) ≤ hammingNorm f := by
  induction m with
  | zero =>
      intro r hr f _hf hne
      have hr0 : r = 0 := by omega
      subst r
      have hpos : 1 ≤ hammingNorm f := hammingNorm_pos_iff.mpr hne
      simpa only [Nat.sub_self, pow_zero] using hpos
  | succ m ih =>
      intro r hr f hf hne
      by_cases htop : r = m + 1
      · subst r
        have hpos : 1 ≤ hammingNorm f := hammingNorm_pos_iff.mpr hne
        simpa only [Nat.sub_self, pow_zero] using hpos
      have hrm : r ≤ m := by omega
      cases r with
      | zero =>
          simpa only [Nat.sub_zero] using (zero_order_weight (m + 1) f hf hne).ge
      | succ r =>
          have hslices := Paper6HalfDecomposition.rm_slices_of_mem m r f hf
          by_cases hdelta : half0 f + half1 f = 0
          · have hequal : half1 f = half0 f := by
              funext x
              have hx := congrFun hdelta x
              have hbit : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
              exact hbit _ _ hx
            have hnonzero : half0 f ≠ 0 := by
              intro hz
              exact hne (eq_zero_of_halves_zero m f hz (hequal.trans hz))
            have hhalf := ih (r + 1) hrm (half0 f) hslices.1 hnonzero
            have hexponent : m + 1 - (r + 1) = (m - (r + 1)) + 1 := by omega
            calc
              2 ^ (m + 1 - (r + 1)) = 2 ^ (m - (r + 1)) * 2 := by
                rw [hexponent, pow_succ]
              _ ≤ hammingNorm (half0 f) * 2 := Nat.mul_le_mul_right 2 hhalf
              _ = hammingNorm f := by
                rw [Paper6HalfDecomposition.weight_slices, hequal]
                omega
          · have hlower := ih r (by omega) (half0 f + half1 f) hslices.2 hdelta
            have hinter := Paper6HalfDecomposition.weight_add_with_intersection
              (half0 f) (half1 f)
            have hsum := Paper6HalfDecomposition.weight_slices m f
            have hcompare : hammingNorm (half0 f + half1 f) ≤ hammingNorm f := by
              omega
            have hexponent : m + 1 - (r + 1) = m - r := by omega
            rw [hexponent]
            exact hlower.trans hcompare

/-- Multiplication by a new last variable extends a word to slices zero and g. -/
def liftLast {m : ℕ} (g : BFun m) : BFun (m + 1) :=
  fun y => y (Fin.last m) * g (Fin.init y)

/-- The zero slice of the recursive witness is identically zero. -/
theorem half0_liftLast {m : ℕ} (g : BFun m) : half0 (liftLast g) = 0 := by
  funext x
  change
    (Fin.snoc (α := fun _ => ZMod 2) x 0) (Fin.last m) *
      g (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 0)) = 0
  rw [Fin.snoc_last, zero_mul]

/-- The one slice of the recursive witness is exactly the previous witness. -/
theorem half1_liftLast {m : ℕ} (g : BFun m) : half1 (liftLast g) = g := by
  funext x
  change
    (Fin.snoc (α := fun _ => ZMod 2) x 1) (Fin.last m) *
      g (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 1)) = g x
  rw [Fin.snoc_last, Fin.init_snoc, one_mul]

/-- The complete polynomial construction from Lem22 certifies the recursive witness. -/
theorem liftLast_mem_RM {m : ℕ} (r : ℕ) (g : BFun m) (hg : g ∈ RM r m) :
    liftLast g ∈ RM (r + 1) (m + 1) := by
  apply Paper6HalfDecomposition.rm_mem_of_slices m r (liftLast g)
  · rw [half0_liftLast]
    exact zero_mem_RM (r + 1) m
  · rw [half0_liftLast, half1_liftLast, zero_add]
    exact hg

/-- Adding a zero slice preserves the weight exactly. -/
theorem liftLast_weight {m : ℕ} (g : BFun m) : hammingNorm (liftLast g) = hammingNorm g := by
  rw [Paper6HalfDecomposition.weight_slices, half0_liftLast, half1_liftLast,
    hammingNorm_zero, zero_add]

/-- An attained minimum-weight codeword for every admissible pair (r,m). -/
theorem minimum_weight_attained (m : ℕ) :
    ∀ r : ℕ, r ≤ m → IsWeight r m (2 ^ (m - r)) := by
  induction m with
  | zero =>
      intro r hr
      have hr0 : r = 0 := by omega
      subst r
      refine ⟨1, one_mem_RM 0 0, ?_⟩
      simpa only [Nat.sub_zero] using hammingNorm_one 0
  | succ m ih =>
      intro r hr
      cases r with
      | zero =>
          refine ⟨1, one_mem_RM 0 (m + 1), ?_⟩
          simpa only [Nat.sub_zero] using hammingNorm_one (m + 1)
      | succ r =>
          obtain ⟨g, hg, hweight⟩ := ih r (by omega)
          refine ⟨liftLast g, liftLast_mem_RM r g hg, ?_⟩
          rw [liftLast_weight, hweight]
          congr 1
          omega

/-- Exact frozen minimum-distance contract, including both the universal bound and the witness. -/
theorem minDist : BackfillPaper6.V3.MinDist := by
  intro r m hr
  exact ⟨nonzero_weight_lower_bound m r hr, minimum_weight_attained m r hr⟩

/-- Exact contract check; this alias does not count as another result. -/
theorem check_MinDist : BackfillPaper6.V3.MinDist := minDist

end Paper6MinDistance

#print axioms Paper6MinDistance.zero_mem_RM
#print axioms Paper6MinDistance.one_mem_RM
#print axioms Paper6MinDistance.hammingNorm_one
#print axioms Paper6MinDistance.rm_zero_order_eq_zero_or_one
#print axioms Paper6MinDistance.zero_order_weight
#print axioms Paper6MinDistance.eq_zero_of_halves_zero
#print axioms Paper6MinDistance.nonzero_weight_lower_bound
#print axioms Paper6MinDistance.half0_liftLast
#print axioms Paper6MinDistance.half1_liftLast
#print axioms Paper6MinDistance.liftLast_mem_RM
#print axioms Paper6MinDistance.liftLast_weight
#print axioms Paper6MinDistance.minimum_weight_attained
#print axioms Paper6MinDistance.minDist
#print axioms Paper6MinDistance.check_MinDist
#print Paper6MinDistance.check_MinDist
