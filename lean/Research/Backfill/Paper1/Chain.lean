import Research.Backfill.Paper1.Additional

/-!
Proof source for the full frozen Lemma23. Compilation and acceptance evidence
are recorded separately; this header makes no acceptance claim.

The tail recurrence is proved in arbitrary dimension directly for the frozen
zRev. No a = 2 result is used. The cell identity is an exact opposite-ray
identity, and the first chain may have length zero or the full width b.
Frozen Challenge SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset

namespace Chain

lemma tMulVec_scale_of_eq (a : ℕ) (p α : ℝ) (c g : ℕ → ℝ)
    (h : ∀ i ≤ a, c i = α * g i) (u : ℕ) :
    Challenge.tMulVec a p c u = α * Challenge.tMulVec a p g u := by
  unfold Challenge.tMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  ring

lemma norm_scale_of_eq (a : ℕ) (p α : ℝ) (c g : ℕ → ℝ)
    (h : ∀ i ≤ a, c i = α * g i) :
    Challenge.l1 a (Challenge.tMulVec a p c) =
      |α| * Challenge.l1 a (Challenge.tMulVec a p g) := by
  unfold Challenge.l1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [tMulVec_scale_of_eq a p α c g h u, abs_mul]

lemma delta_sign_scale (a : ℕ) (p : ℝ) (l : ℕ) (c g : ℕ → ℝ)
    (h : ∀ i ≤ a, c i = (-1) ^ l * g i) :
    Challenge.DeltaC a p c = Challenge.DeltaC a p g := by
  unfold Challenge.DeltaC
  rw [norm_scale_of_eq a p ((-1) ^ l) c g h, abs_neg_one_pow, one_mul]

/-- The exact index conversion, valid also at l = 0 and l = b. -/
lemma zeta_reverse (b : ℕ) (q : ℝ) (Y : ℕ → ℕ → ℝ) (i l : ℕ) :
    Challenge.zetaPath b q Y ((b : ℤ) - 1 - l) i =
      Challenge.zRev q b (Y i) l := by
  unfold Challenge.zetaPath Challenge.z
  congr 1
  omega

lemma tail_state (a b : ℕ) (q : ℝ) (Y : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (k : ℕ) (hk : k ≤ b) (hLast : ∀ i ≤ a, Y i b = g i)
    (hTail : ∀ l, 1 ≤ l → l ≤ k → ∀ i ≤ a, Y i (b - l) = (-1) ^ l * g i) :
    ∀ l ≤ k, ∀ i ≤ a,
      Challenge.zetaPath b q Y ((b : ℤ) - 1 - l) i =
        (-1) ^ l * Challenge.mu q ((l : ℤ) - 1) * g i := by
  intro l hl i hi
  rw [zeta_reverse, Additional.mu_pred_eq_nu]
  have hrec : ∀ d ≤ k,
      Challenge.zRev q b (Y i) d = (-1) ^ d * ICGGeneral.nu q d * g i := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa only [Challenge.zRev, pow_zero, ICGGeneral.nu_zero, one_mul] using hLast i hi
    | succ d ih =>
      intro hd
      have hindex : b - 1 - d = b - (d + 1) := by omega
      rw [Challenge.zRev, ih (by omega), hindex, hTail (d + 1) (by omega) hd i hi,
        ICGGeneral.nu_succ, pow_succ]
      ring
  exact hrec l hl

/-- A point on the opposite ray, no further than P times A, has zero cell.
The cell parameter μ is arbitrary; it is not assumed equal to the ray ratio. -/
lemma hcell_opposite_ray (P μ t A : ℝ) (ht : 0 ≤ t) (htP : t ≤ P) :
    Challenge.hcell P μ A (-t * A) = 0 := by
  have h1 : 0 ≤ 1 + t := by linarith
  have h2 : 0 ≤ P - t := sub_nonneg.mpr htP
  unfold Challenge.hcell
  rw [show A - -t * A = (1 + t) * A by ring,
    show -t * A + P * A = (P - t) * A by ring]
  simp only [abs_mul, abs_neg, abs_of_nonneg ht, abs_of_nonneg h1, abs_of_nonneg h2]
  ring

lemma tail_psi {q : ℝ} (hq : 2 < q) (a b : ℕ) (p : ℝ)
    (Y : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (k : ℕ) (hk : k ≤ b)
    (hLast : ∀ i ≤ a, Y i b = g i)
    (hTail : ∀ l, 1 ≤ l → l ≤ k → ∀ i ≤ a, Y i (b - l) = (-1) ^ l * g i) :
    ∀ l, 1 ≤ l → l ≤ k →
      Challenge.psiCol a b p q Y (b - l) =
        (q - 1) * (1 + Challenge.mu q ((b : ℤ) - l - 1)) * Challenge.DeltaC a p g := by
  intro l hl1 hlk
  have hcol : ∀ i ≤ a, Challenge.col Y (b - l) i = (-1) ^ l * g i :=
    hTail l hl1 hlk
  have hstate := tail_state a b q Y g k hk hLast hTail (l - 1) (by omega)
  have hindex : (b : ℤ) - 1 - ((l - 1 : ℕ) : ℤ) = ((b - l : ℕ) : ℤ) := by omega
  rw [hindex] at hstate
  have hzeta : ∀ i ≤ a, Challenge.zetaPath b q Y (((b - l : ℕ) : ℤ)) i =
      (((-1 : ℝ) ^ (l - 1)) * ICGGeneral.nu q (l - 1)) * g i := by
    intro i hi
    simpa only [Additional.mu_pred_eq_nu] using hstate i hi
  have hsign : (-1 : ℝ) ^ l = -((-1 : ℝ) ^ (l - 1)) := by
    conv_lhs => rw [show l = (l - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hcell : ∀ u ∈ range (a + 1),
      Challenge.hcell (q - 1) (Challenge.mu q (((b - l : ℕ) : ℤ) - 1))
        (Challenge.tMulVec a p (Challenge.col Y (b - l)) u)
        (Challenge.tMulVec a p (Challenge.zetaPath b q Y (((b - l : ℕ) : ℤ))) u) = 0 := by
    intro u _
    have hrel : Challenge.tMulVec a p (Challenge.zetaPath b q Y (((b - l : ℕ) : ℤ))) u =
        -(ICGGeneral.nu q (l - 1)) * Challenge.tMulVec a p (Challenge.col Y (b - l)) u := by
      rw [tMulVec_scale_of_eq a p _ _ g hzeta u,
        tMulVec_scale_of_eq a p _ _ g hcol u, hsign]
      ring
    rw [hrel]
    exact hcell_opposite_ray _ _ _ _ (ICGGeneral.nu_pos hq _).le
      (le_trans (ICGGeneral.nu_bounds hq.le _).2 (by linarith))
  unfold Challenge.psiCol Challenge.psi
  rw [delta_sign_scale a p l (Challenge.col Y (b - l)) g hcol,
    Finset.sum_eq_zero hcell, sub_zero]
  rw [show ((b - l : ℕ) : ℤ) - 1 = (b : ℤ) - l - 1 by omega]

lemma sign_add_even (n d : ℕ) : (-1 : ℝ) ^ (n + 2 * d) = (-1 : ℝ) ^ n := by
  rw [pow_add, pow_mul]
  norm_num

lemma sign_reverse (b l : ℕ) (hl : l ≤ b) :
    (-1 : ℝ) ^ l * (-1 : ℝ) ^ (b + 1) = (-1 : ℝ) ^ (b - l + 1) := by
  rw [← pow_add, show l + (b + 1) = (b - l + 1) + 2 * l by omega, sign_add_even]

lemma anti_tail (a b : ℕ) (q : ℝ) (Y : ℕ → ℕ → ℝ) (J : ℕ) (hJ : J < b)
    (hTail : ∀ l, J < l → l ≤ b → ∀ i ≤ a, Y i l = (-1) ^ (l + 1) * Challenge.sAlt i) :
    ∀ i ≤ a, Challenge.zetaPath b q Y J i =
      (-1) ^ J * Challenge.mu q ((b : ℤ) - 2 - J) * Challenge.sAlt i := by
  let g : ℕ → ℝ := fun i => (-1) ^ (b + 1) * Challenge.sAlt i
  let k : ℕ := b - (J + 1)
  have hk : k ≤ b := Nat.sub_le _ _
  have hLast : ∀ i ≤ a, Y i b = g i := by
    intro i hi
    exact hTail b hJ le_rfl i hi
  have hchain : ∀ l, 1 ≤ l → l ≤ k → ∀ i ≤ a, Y i (b - l) = (-1) ^ l * g i := by
    intro l _hl hlk i hi
    have hjl : J < b - l := by dsimp only [k] at hlk; omega
    rw [hTail (b - l) hjl (Nat.sub_le _ _) i hi]
    dsimp only [g]
    rw [← mul_assoc, sign_reverse b l (by omega)]
  have hs := tail_state a b q Y g k hk hLast hchain k le_rfl
  have hidx : (b : ℤ) - 1 - (k : ℤ) = (J : ℤ) := by dsimp only [k]; omega
  have hmu : (k : ℤ) - 1 = (b : ℤ) - 2 - J := by dsimp only [k]; omega
  have hexp : k + (b + 1) = J + 2 * (b - J) := by
    dsimp only [k]
    omega
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (b + 1) = (-1 : ℝ) ^ J := by
    rw [← pow_add, hexp, sign_add_even]
  rw [hidx, hmu] at hs
  intro i hi
  rw [hs i hi]
  dsimp only [g]
  calc
    (-1 : ℝ) ^ k * Challenge.mu q ((b : ℤ) - 2 - J) *
        ((-1 : ℝ) ^ (b + 1) * Challenge.sAlt i) =
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (b + 1)) *
        Challenge.mu q ((b : ℤ) - 2 - J) * Challenge.sAlt i := by ring
    _ = _ := by rw [hsign]

end Chain

theorem check_Lemma23 : Challenge.Lemma23 := by
  intro a b _ha _hb _hab p q hregions Y _hY
  have hq : 2 < q := by
    rcases hregions with ⟨_, hq⟩ | ⟨_, hq⟩ <;> linarith
  constructor
  · intro g _hg k hk hLast hTail
    exact ⟨Chain.tail_state a b q Y g k hk hLast hTail,
      Chain.tail_psi hq a b p Y g k hk hLast hTail⟩
  · intro J hJ hTail
    exact Chain.anti_tail a b q Y J hJ hTail

#print axioms check_Lemma23
end CodexPaper1
