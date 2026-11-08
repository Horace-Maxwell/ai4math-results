import Research.Backfill.Paper1.Challenge
import Research.ICGGeneralThm5
import Research.ICGEqualParityLemmas

/-!
# Paper 1: exact bridges for frozen Lemmas 11, 18 and 20

Frozen contract SHA-256:
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.

The three `check_` declarations use the complete frozen types without additional
hypotheses. The local check_additional.py script records compilation, axiom,
kernel-checker and new-directory replay evidence separately from this source.

The entry bridge is restricted to the actual matrix square `0..m`, since the
two representations intentionally need not agree outside that square. The path
bridge uses the exact index shift `z_j = Zp (j+1)` and is only applied for j<m.
-/

set_option autoImplicit false

namespace CodexPaper1

open BackfillPaper1 Finset

namespace Additional

/-- The explicit matrix in the contract equals the weighted Ramanujan matrix
on its actual rows and columns. No positivity assumption is needed here. -/
lemma tEntry_eq_Tent (x : ℝ) (m i j : ℕ) (hi : i ≤ m) (hj : j ≤ m) :
    Challenge.tEntry m x i j = ICGGeneral.Tent x m i j := by
  by_cases him : i < m
  · by_cases hjm : j < m
    · have hmi : m - i ≠ 0 := by omega
      have hmj : m - j ≠ 0 := by omega
      by_cases hlo : i + j + 2 ≤ m
      · have hle : ¬ m - j ≤ i := by omega
        have he : ¬ m - j = i + 1 := by omega
        simp [Challenge.tEntry, him, hjm, hlo, ICGGeneral.Tent,
          ICGGeneral.ramX, hmj, hle, he]
      · by_cases heq : i + j + 1 = m
        · have hle : ¬ m - j ≤ i := by omega
          have he : m - j = i + 1 := by omega
          simp only [Challenge.tEntry, ite_eq_left (And.intro him hjm), ite_eq_right hlo,
            ite_eq_left heq, ICGGeneral.Tent, ICGGeneral.ramX, ite_eq_right hmj,
            ite_eq_right hle, ite_eq_left he, ICGGeneral.phiX, ite_eq_right hmi]
          have hexp : m - 1 = (m - i - 1) + i := by omega
          rw [hexp, pow_add]
          ring
        · have hle : m - j ≤ i := by omega
          simp only [Challenge.tEntry, ite_eq_left (And.intro him hjm), ite_eq_right hlo,
            ite_eq_right heq, ICGGeneral.Tent, ICGGeneral.ramX, ite_eq_left hle,
            ICGGeneral.phiX, ite_eq_right hmi, ite_eq_right hmj]
          have hexp : 2 * m - i - j - 2 = (m - i - 1) + (m - j - 1) := by omega
          rw [hexp, pow_add]
          ring
    · have hje : j = m := by omega
      subst j
      have hmi : m - i ≠ 0 := by omega
      simp [Challenge.tEntry, him, ICGGeneral.Tent, ICGGeneral.ramX,
        ICGGeneral.phiX, hmi]
  · have hie : i = m := by omega
    subst i
    by_cases hjm : j < m
    · have hmj : m - j ≠ 0 := by omega
      have hle : m - j ≤ m := by omega
      simp [Challenge.tEntry, hjm, ICGGeneral.Tent, ICGGeneral.ramX,
        ICGGeneral.phiX, hmj, hle]
    · have hje : j = m := by omega
      subst j
      simp [Challenge.tEntry, ICGGeneral.Tent, ICGGeneral.ramX, ICGGeneral.phiX]

lemma tMulVec_eq_Tv (x : ℝ) (m : ℕ) (w : ℕ → ℝ) (u : ℕ) (hu : u ≤ m) :
    Challenge.tMulVec m x w u = ICGGeneral.Tv x m w u := by
  unfold Challenge.tMulVec ICGGeneral.Tv
  apply Finset.sum_congr rfl
  intro j hj
  rw [tEntry_eq_Tent x m u j hu (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

lemma l1_tMulVec_eq_L1 (x : ℝ) (m : ℕ) (w : ℕ → ℝ) :
    Challenge.l1 m (Challenge.tMulVec m x w) = ICGGeneral.L1 x m w := by
  unfold Challenge.l1 ICGGeneral.L1
  apply Finset.sum_congr rfl
  intro u hu
  rw [tMulVec_eq_Tv x m w u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]

lemma dNorm_eq_L1 (x : ℝ) (m : ℕ) :
    Challenge.dNorm m x = ICGGeneral.L1 x m ICGGeneral.sgnv := by
  exact l1_tMulVec_eq_L1 x m Challenge.sAlt

/-- Both recurrences start at 1; their natural index counts are identical. -/
lemma muSeq_eq_nu (x : ℝ) (n : ℕ) : Challenge.muSeq x n = ICGGeneral.nu x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Challenge.muSeq, ICGGeneral.nu, ih]

lemma mu_pred_eq_nu (x : ℝ) (j : ℕ) :
    Challenge.mu x ((j : ℤ) - 1) = ICGGeneral.nu x j := by
  unfold Challenge.mu
  rw [sub_add_cancel, Int.toNat_natCast, muSeq_eq_nu]

lemma mu_nat_eq_nu (x : ℝ) (j : ℕ) :
    Challenge.mu x (j : ℤ) = ICGGeneral.nu x (j + 1) := by
  unfold Challenge.mu
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega,
    Int.toNat_natCast, muSeq_eq_nu]

lemma cc_eq (x : ℝ) (j : ℕ) :
    Challenge.cc x (j : ℤ) = ICGGeneral.cc x j := by
  unfold Challenge.cc ICGGeneral.cc
  rw [mu_pred_eq_nu]

/-- The reversed recursive path equals the sum-defined path at `m-d`. -/
lemma zRev_eq_Zp {x : ℝ} (hx : x ≠ 0) (m : ℕ) (w : ℕ → ℝ) (d : ℕ) (hd : d ≤ m) :
    Challenge.zRev x m w d = ICGGeneral.Zp x m w (m - d) := by
  revert hd
  induction d with
  | zero =>
    intro _hd
    simp [Challenge.zRev, ICGGeneral.Zp_self]
  | succ d ih =>
    intro hd
    have hidx : m - 1 - d = m - (d + 1) := by omega
    have hnext : m - (d + 1) + 1 = m - d := by omega
    rw [Challenge.zRev, ih (by omega), hidx,
      ICGGeneral.Zp_rec hx m w (k := m - (d + 1)) (by omega), hnext]

lemma z_nat_eq_Zp {x : ℝ} (hx : x ≠ 0) (m : ℕ) (w : ℕ → ℝ) (j : ℕ) (hj : j < m) :
    Challenge.z x m w (j : ℤ) = ICGGeneral.Zp x m w (j + 1) := by
  have hidx : ((m : ℤ) - 1 - (j : ℤ)).toNat = m - (j + 1) := by omega
  rw [Challenge.z, hidx, zRev_eq_Zp hx m w (m - (j + 1)) (by omega),
    show m - (m - (j + 1)) = j + 1 by omega]

/-- A sign vector that is not `±s` must have an adjacent repetition. -/
lemma exists_repeat_of_not_pmAlt {m : ℕ} {y : ℕ → ℝ}
    (hy : Challenge.IsSignVec m y) (hna : ¬ Challenge.IsPmAlt m y) :
    ∃ j < m, y j = y (j + 1) := by
  classical
  by_contra hn
  have halt : ∀ j < m, y j ≠ y (j + 1) := by
    intro j hj he
    exact hn ⟨j, hj, he⟩
  have hpm := ICGGeneral.alternating_eq (show ICGGeneral.IsSign m y from hy) halt
  apply hna
  exact hpm

/-- The released slack is twice the paper's sigma, with its exact integer
potential index and its filtered nonalternation set. -/
lemma slack_eq_two_sigma {x : ℝ} (hx : x ≠ 0) (m : ℕ) (y : ℕ → ℝ) :
    ICGGeneral.slack x m y =
      2 * (∑ j ∈ Challenge.NA m y, Challenge.mu x (j : ℤ) * |Challenge.z x m y (j : ℤ)|) := by
  classical
  unfold ICGGeneral.slack Challenge.NA
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < m := Finset.mem_range.mp hj
  by_cases he : y j = y (j + 1)
  · simp only [ite_eq_left he, mu_nat_eq_nu, z_nat_eq_Zp hx m y j hjm]
    ring
  · simp only [ite_eq_right he, mul_zero]

end Additional

open Additional

theorem check_Lemma11 : Challenge.Lemma11 := by
  intro q hq b _hb P μ hP hμ0 hμ1 y ζ hy hζ
  dsimp only
  rw [dNorm_eq_L1]
  simp only [l1_tMulVec_eq_L1]
  refine ⟨ICGGeneral.local_ineq hq hP hμ0 hμ1 hy hζ, ?_⟩
  intro hna
  exact ICGGeneral.local_ineq_strict hq hP hμ0 hμ1 hy hζ
    (exists_repeat_of_not_pmAlt hy hna)

theorem check_Lemma18 : Challenge.Lemma18 := by
  intro x hx m _hm w
  have hx0 : 0 < x := by linarith
  have hsum1 : (∑ j ∈ range m, Challenge.cc x (j : ℤ) * |w j|) =
      ∑ j ∈ range m, ICGGeneral.cc x j * |w j| := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [cc_eq]
  have hsum2 : (∑ j ∈ range m,
      Challenge.hcell (x - 1) (Challenge.mu x ((j : ℤ) - 1)) (w j)
        (Challenge.z x m w (j : ℤ))) =
      ∑ j ∈ range m, ICGGeneral.hcell (x - 1) (ICGGeneral.nu x j) (w j)
        (ICGGeneral.Zp x m w (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mu_pred_eq_nu, z_nat_eq_Zp hx0.ne' m w j (Finset.mem_range.mp hj)]
    rfl
  rw [l1_tMulVec_eq_L1, hsum1, mu_pred_eq_nu, hsum2,
    ICGEqualParity.L1_potential hx m w]
  field_simp [hx0.ne']

theorem check_Lemma20 : Challenge.Lemma20 := by
  intro x R hparam m _hm hmOdd y hy hends
  have hx3 : 3 ≤ x := by
    rcases hparam with h | h <;> linarith [h.1]
  have hR1 : 1 ≤ R := by
    rcases hparam with h | h <;> linarith [h.2]
  have h := ICGEqualParity.lemmaB hx3 hR1 hmOdd
    (show ICGGeneral.IsSign m y from hy) hends
  rw [← mu_pred_eq_nu x m, slack_eq_two_sigma (show x ≠ 0 by linarith) m y] at h
  nlinarith only [h]

#print axioms check_Lemma11
#print axioms check_Lemma18
#print axioms check_Lemma20

end CodexPaper1
