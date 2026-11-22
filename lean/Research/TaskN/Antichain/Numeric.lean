import Mathlib

namespace TaskN.Antichain.Num

/-- A spine site carries a bare vertex, a type-B gadget, or a type-A gadget. -/
abbrev Cell := Option Bool

def hEval (x : ℝ) : ℝ :=
  1 + 9 * x + 28 * x ^ 2 + 42 * x ^ 3 + 39 * x ^ 4 + 22 * x ^ 5 + 7 * x ^ 6 + x ^ 7

def aEval (x : ℝ) : ℝ :=
  1 + 10 * x + 36 * x ^ 2 + 65 * x ^ 3 + 75 * x ^ 4 + 57 * x ^ 5 + 28 * x ^ 6 + 8 * x ^ 7 + x ^ 8

def bEval (x : ℝ) : ℝ :=
  1 + 10 * x + 36 * x ^ 2 + 64 * x ^ 3 + 66 * x ^ 4 + 41 * x ^ 5 + 14 * x ^ 6 + 2 * x ^ 7


/-- Contribution when the spine vertex is unoccupied. -/
def p (k : Cell) (x : ℝ) : ℝ :=
  match k with
  | none => 1
  | some false => bEval x
  | some true => aEval x

/-- Contribution when the spine vertex is occupied (the gadget root is forbidden). -/
def q (k : Cell) (x : ℝ) : ℝ :=
  match k with
  | none => x
  | some _ => x * hEval x

/-- Total and root-forbidden sums for a decorated path, read from left to right. -/
def val : List Cell → ℝ → ℝ × ℝ
  | [], _ => (1,1)
  | k :: tail, x =>
    let s := val tail x
    (p k x * s.1 + q k x * s.2, p k x * s.1)

def family (m j pad : ℕ) : List Cell :=
  List.replicate j (some true) ++ List.replicate (m-j) (some false) ++ List.replicate pad none

/-- Taylor expansion at -1/6 gives certificates with strictly positive coefficients. -/
theorem hEval_pos {x : ℝ} (hx : -(1/6 : ℝ) ≤ x) : 0 < hEval x := by
  let u := x + 1/6
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have certificate : hEval x = (31001/279936 + u * (117763/46656 + u * (32555/2592 + u * (27851/1296 + u * (5059/216 + u * (187/12 + u * (35/6 + u * (1:ℝ)))))))) := by
    unfold hEval
    dsimp [u]
    ring
  rw [certificate]
  positivity

theorem aEval_margin {x : ℝ} (hx : -(1/6 : ℝ) ≤ x) : 0 < aEval x + 4 * (x * hEval x) := by
  let u := x + 1/6
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have certificate : aEval x + 4 * (x * hEval x) = (16277/1679616 + u * (34555/34992 + u * (179477/11664 + u * (15640/243 + u * (70159/648 + u * (3151/27 + u * (701/9 + u * (88/3 + u * (5:ℝ))))))))) := by
    unfold aEval hEval
    dsimp [u]
    ring
  rw [certificate]
  positivity

theorem bEval_margin {x : ℝ} (hx : -(1/6 : ℝ) ≤ x) : 0 < bEval x + 4 * (x * hEval x) := by
  let u := x + 1/6
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have certificate : bEval x + 4 * (x * hEval x) = (961/104976 + u * (71317/69984 + u * (174745/11664 + u * (128419/1944 + u * (34891/324 + u * (6019/54 + u * (631/9 + u * (74/3 + u * (4:ℝ))))))))) := by
    unfold bEval hEval
    dsimp [u]
    ring
  rw [certificate]
  positivity


theorem site_bounds (k : Cell) {x : ℝ} (hx : x ∈ Set.Icc (-(1/6 : ℝ)) 0) :
    q k x ≤ 0 ∧ 0 < p k x + 4 * q k x := by
  rcases hx with ⟨hlo, hhi⟩
  cases k with
  | none =>
    change x ≤ 0 ∧ 0 < 1 + 4*x
    exact ⟨hhi, by linarith⟩
  | some k =>
    have hq := mul_nonpos_of_nonpos_of_nonneg hhi (hEval_pos hlo).le
    cases k
    · exact ⟨hq,bEval_margin hlo⟩
    · exact ⟨hq,aEval_margin hlo⟩

/-- The invariant avoids division even when the site is bare or x is zero. -/
theorem val_bounds (cells : List Cell) {x : ℝ} (hx : x ∈ Set.Icc (-(1/6 : ℝ)) 0) :
    0 < (val cells x).1 ∧ 0 < (val cells x).2 ∧ (val cells x).2 ≤ 2*(val cells x).1 := by
  induction cells with
  | nil => norm_num [val]
  | cons k tail ih =>
    obtain ⟨hz,_,hsz⟩ := ih
    obtain ⟨hq,hmargin⟩ := site_bounds k hx
    have hp : 0 < p k x := by linarith
    have hqs := mul_le_mul_of_nonpos_left hsz hq
    have hmul := mul_pos hmargin hz
    have hs := mul_pos hp hz
    change 0 < p k x * (val tail x).1 + q k x * (val tail x).2 ∧
      0 < p k x * (val tail x).1 ∧
      p k x * (val tail x).1 ≤ 2*(p k x * (val tail x).1 + q k x * (val tail x).2)
    refine ⟨?_,hs,?_⟩ <;> nlinarith only [hqs,hmul,hs]

theorem val_pos (cells : List Cell) {x : ℝ} (hx : x ∈ Set.Icc (-(1/6 : ℝ)) 0) :
    0 < (val cells x).1 := (val_bounds cells hx).1

/-- At a replacement, the occupied-site contribution cancels. Propagation through
the prefix is linear and starts from equal total and forbidden differences. -/
theorem swap_delta (pre post : List Cell) (x : ℝ) :
    (val (pre ++ some true :: post) x).1 - (val (pre ++ some false :: post) x).1 =
        (aEval x-bEval x) * (val post x).1 * (val pre x).1 ∧
    (val (pre ++ some true :: post) x).2 - (val (pre ++ some false :: post) x).2 =
        (aEval x-bEval x) * (val post x).1 * (val pre x).2 := by
  induction pre with
  | nil =>
    simp only [List.nil_append, val, p, q]
    constructor <;> ring
  | cons k pre ih =>
    simp only [List.cons_append, val]
    constructor
    · linear_combination (p k x) * ih.1 + (q k x) * ih.2
    · linear_combination (p k x) * ih.1

private theorem step_delta (m j pad : ℕ) (hj : j < m) (x : ℝ) :
    (val (family m (j+1) pad) x).1 - (val (family m j pad) x).1 =
    (aEval x-bEval x) *
      (val (List.replicate (m-(j+1)) (some false) ++ List.replicate pad none) x).1 *
      (val (List.replicate j (some true)) x).1 := by
  have he : m-j = (m-(j+1))+1 := by omega
  have hA : family m (j+1) pad =
      List.replicate j (some true) ++ some true ::
        (List.replicate (m-(j+1)) (some false) ++ List.replicate pad none) := by
    unfold family
    rw [List.replicate_succ']
    simp [List.append_assoc]
  have hB : family m j pad =
      List.replicate j (some true) ++ some false ::
        (List.replicate (m-(j+1)) (some false) ++ List.replicate pad none) := by
    unfold family
    rw [he, List.replicate_succ]
    simp [List.append_assoc]
  rw [hA,hB]
  exact (swap_delta _ _ _).1

private theorem family_step_10 (m j pad : ℕ) (hj : j < m) :
    (val (family m (j+1) pad) (-(1/10:ℝ))).1 < (val (family m j pad) (-(1/10:ℝ))).1 := by
  have hx : -(1/10:ℝ) ∈ Set.Icc (-(1/6:ℝ)) 0 := by constructor <;> norm_num
  have hg : aEval (-(1/10:ℝ))-bEval (-(1/10:ℝ)) < 0 := by norm_num [aEval,bEval]
  apply sub_neg.mp
  rw [step_delta m j pad hj]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hg (val_pos _ hx)) (val_pos _ hx)

private theorem family_step_6 (m j pad : ℕ) (hj : j < m) :
    (val (family m j pad) (-(1/6:ℝ))).1 < (val (family m (j+1) pad) (-(1/6:ℝ))).1 := by
  have hx : -(1/6:ℝ) ∈ Set.Icc (-(1/6:ℝ)) 0 := by constructor <;> norm_num
  have hg : 0 < aEval (-(1/6:ℝ))-bEval (-(1/6:ℝ)) := by norm_num [aEval,bEval]
  apply sub_pos.mp
  rw [step_delta m j pad hj]
  exact mul_pos (mul_pos hg (val_pos _ hx)) (val_pos _ hx)

theorem family_strict_10 {m i j : ℕ} (pad : ℕ) (hij : i < j) (hjm : j ≤ m) :
    (val (family m j pad) (-(1/10:ℝ))).1 < (val (family m i pad) (-(1/10:ℝ))).1 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := family_step_10 m j pad (by omega)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with h | h
    · subst i; exact hstep
    · exact lt_trans hstep (ih h (by omega))

theorem family_strict_6 {m i j : ℕ} (pad : ℕ) (hij : i < j) (hjm : j ≤ m) :
    (val (family m i pad) (-(1/6:ℝ))).1 < (val (family m j pad) (-(1/6:ℝ))).1 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := family_step_6 m j pad (by omega)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with h | h
    · subst i; exact hstep
    · exact lt_trans (ih h (by omega)) hstep

end TaskN.Antichain.Num
