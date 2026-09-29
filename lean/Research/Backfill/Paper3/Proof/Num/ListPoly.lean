import Mathlib

/-!
# Verified list polynomials for kernel computation

Coefficient lists `List ℕ` (constant term first) with sum, scaling, product, truncation and
prefix sums, written directly with the recursors `List.rec` / `Nat.rec` and the kernel-accelerated
`Nat` operations, so that `decide +kernel` evaluates them quickly. Each operation is proved
correct against `toPoly : List ℕ → ℤ[X]`; `Approx T a p` says that the coefficients of `a` and
`p` below `T` agree, and truncated products preserve it.
-/

set_option autoImplicit false

namespace P3Num

open Finset Polynomial

/-! ### The computational layer -/

/-- Pointwise sum of two coefficient lists. -/
def addL (a b : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun b => b)
    (fun x _ ih b => List.rec (motive := fun _ => List ℕ) (x :: ih [])
      (fun y b' _ => Nat.add x y :: ih b') b) a b

/-- `c · a`. -/
def scaleL (c : ℕ) (a : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun x _ ih => Nat.mul c x :: ih) a

/-- The product `b · a` (the loop runs over the first factor, which should be the short one;
zero coefficients of `b` are skipped). -/
def mulL (b a : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun c _ ih => cond (Nat.beq c 0) (0 :: ih) (addL (scaleL c a) (0 :: ih))) b

/-- The first `n` coefficients. -/
def takeL (n : ℕ) (a : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => [])
    (fun _ ih a => List.rec (motive := fun _ => List ℕ) [] (fun x a' _ => x :: ih a') a) n a

/-- The sum of the entries. -/
def sumL (a : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x ih) a

@[simp] theorem addL_nil (b : List ℕ) : addL [] b = b := rfl

@[simp] theorem addL_cons_nil (x : ℕ) (a : List ℕ) : addL (x :: a) [] = x :: addL a [] := rfl

@[simp] theorem addL_cons_cons (x y : ℕ) (a b : List ℕ) :
    addL (x :: a) (y :: b) = (x + y) :: addL a b := rfl

@[simp] theorem addL_nil_right (a : List ℕ) : addL a [] = a := by
  induction a with
  | nil => rfl
  | cons x a ih => rw [addL_cons_nil, ih]

@[simp] theorem scaleL_nil (c : ℕ) : scaleL c [] = [] := rfl

@[simp] theorem scaleL_cons (c x : ℕ) (a : List ℕ) : scaleL c (x :: a) = c * x :: scaleL c a := rfl

@[simp] theorem mulL_nil (a : List ℕ) : mulL [] a = [] := rfl

theorem mulL_cons (c : ℕ) (b a : List ℕ) :
    mulL (c :: b) a = cond (Nat.beq c 0) (0 :: mulL b a) (addL (scaleL c a) (0 :: mulL b a)) :=
  rfl

@[simp] theorem takeL_zero (a : List ℕ) : takeL 0 a = [] := rfl

@[simp] theorem takeL_succ_nil (n : ℕ) : takeL (n + 1) [] = [] := rfl

@[simp] theorem takeL_succ_cons (n x : ℕ) (a : List ℕ) :
    takeL (n + 1) (x :: a) = x :: takeL n a := rfl

@[simp] theorem sumL_nil : sumL [] = 0 := rfl

@[simp] theorem sumL_cons (x : ℕ) (a : List ℕ) : sumL (x :: a) = x + sumL a := rfl

/-! ### Correctness -/

/-- The integer polynomial with coefficient list `a`. -/
noncomputable def toPoly : List ℕ → ℤ[X]
  | [] => 0
  | x :: a => (x : ℤ[X]) + X * toPoly a

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

@[simp] theorem toPoly_cons (x : ℕ) (a : List ℕ) : toPoly (x :: a) = (x : ℤ[X]) + X * toPoly a :=
  rfl

theorem toPoly_addL (a b : List ℕ) : toPoly (addL a b) = toPoly a + toPoly b := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp
    | cons y b =>
      rw [addL_cons_cons, toPoly_cons, toPoly_cons, toPoly_cons, ih]
      push_cast
      ring

theorem toPoly_scaleL (c : ℕ) (a : List ℕ) : toPoly (scaleL c a) = (c : ℤ[X]) * toPoly a := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [scaleL_cons, toPoly_cons, toPoly_cons, ih]
    push_cast
    ring

theorem toPoly_mulL (b a : List ℕ) : toPoly (mulL b a) = toPoly b * toPoly a := by
  induction b with
  | nil => simp
  | cons c b ih =>
    rw [mulL_cons]
    cases h : Nat.beq c 0
    · rw [Bool.cond_false, toPoly_addL, toPoly_scaleL, toPoly_cons, ih, toPoly_cons]
      push_cast
      ring
    · rw [Bool.cond_true, toPoly_cons, ih, toPoly_cons, Eq.mp Nat.beq_eq h]
      push_cast
      ring

theorem coeff_toPoly (a : List ℕ) (s : ℕ) : (toPoly a).coeff s = (a.getD s 0 : ℤ) := by
  induction a generalizing s with
  | nil => simp
  | cons x a ih =>
    cases s with
    | zero => simp [coeff_natCast_ite]
    | succ s => simp [coeff_natCast_ite, coeff_X_mul, ih]

theorem getD_takeL (n : ℕ) (a : List ℕ) (s : ℕ) :
    (takeL n a).getD s 0 = if s < n then a.getD s 0 else 0 := by
  induction n generalizing a s with
  | zero => simp
  | succ n ih =>
    cases a with
    | nil => simp
    | cons x a =>
      cases s with
      | zero => simp
      | succ s =>
        rw [takeL_succ_cons, List.getD_cons_succ, ih, List.getD_cons_succ]
        simp only [Nat.add_lt_add_iff_right]

theorem sumL_takeL (n : ℕ) (a : List ℕ) : sumL (takeL n a) = ∑ s ∈ range n, a.getD s 0 := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    cases a with
    | nil => simp
    | cons x a =>
      rw [takeL_succ_cons, sumL_cons, ih, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- The coefficients of `a` and `p` below `T` agree. -/
def Approx (T : ℕ) (a : List ℕ) (p : ℤ[X]) : Prop :=
  ∀ s < T, (toPoly a).coeff s = p.coeff s

theorem approx_toPoly (T : ℕ) (a : List ℕ) : Approx T a (toPoly a) := fun _ _ => rfl

theorem approx_one (T : ℕ) : Approx T [1] 1 := by
  intro s _
  simp

/-- Truncated products preserve `Approx`. -/
theorem approx_mul {T : ℕ} {a b : List ℕ} {p q : ℤ[X]} (ha : Approx T a p) (hb : Approx T b q) :
    Approx T (takeL T (mulL a b)) (p * q) := by
  intro s hs
  rw [coeff_toPoly, getD_takeL, ite_eq_left hs, ← coeff_toPoly, toPoly_mulL, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [ha x.1 (by omega), hb x.2 (by omega)]

/-- `Σ_{s ≤ t} [z^s] p` as a natural number (all our polynomials have nonnegative
coefficients). -/
noncomputable def prefN (p : ℤ[X]) (t : ℕ) : ℕ :=
  (∑ s ∈ range (t + 1), p.coeff s).toNat

theorem cast_sumL_takeL {T : ℕ} {a : List ℕ} {p : ℤ[X]} (h : Approx T a p) {t : ℕ} (ht : t < T) :
    (sumL (takeL (t + 1) a) : ℤ) = ∑ s ∈ range (t + 1), p.coeff s := by
  rw [sumL_takeL]
  push_cast
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← coeff_toPoly, h s (by rw [Finset.mem_range] at hs; omega)]

theorem sumL_takeL_eq_prefN {T : ℕ} {a : List ℕ} {p : ℤ[X]} (h : Approx T a p) {t : ℕ}
    (ht : t < T) : sumL (takeL (t + 1) a) = prefN p t := by
  rw [prefN, ← cast_sumL_takeL h ht, Int.toNat_natCast]

end P3Num
