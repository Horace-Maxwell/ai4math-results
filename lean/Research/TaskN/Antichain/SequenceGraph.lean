import Research.TaskN.Antichain.TreeCode
import Research.TaskN.Antichain.Numeric

namespace TaskN.Antichain

open Polynomial
open _root_.TaskN.Antichain.Num (Cell)

/-- A two-leaf star and a four-leaf star, rooted at their respective centres. -/
private def twoStar : RT := .link (.link .leaf .leaf) .leaf
private def fourStar : RT := .link (.link twoStar .leaf) .leaf

/-- The same nine-point tree with its attachment site at u (true) or v (false).
The new leaf is the interface of the ten-point gadget. -/
private def gadget : Bool → RT
  | true => .link .leaf (.link twoStar (.link .leaf fourStar))
  | false => .link .leaf (.link (.link .leaf twoStar) fourStar)

/-- The root of a site is the backbone vertex. -/
def spineSite : Cell → RT
  | none => .leaf
  | some b => .link .leaf (gadget b)

private theorem site_eval (k : Cell) (x : ℝ) :
    (spineSite k).pair.2.eval x = Num.p k x ∧
    (spineSite k).pair.1.eval x = Num.p k x + Num.q k x := by
  cases k with
  | none =>
    simp [spineSite, RT.pair, Num.p, Num.q]
  | some b =>
    cases b <;> constructor <;>
      simp [spineSite, gadget, twoStar, fourStar, RT.pair,
        Num.p, Num.q, Num.hEval, Num.aEval, Num.bEval] <;> ring

/-- Keeping a left-hand root while joining sites puts edges exactly between
consecutive backbone vertices, regardless of their attached gadgets. -/
def realiseCons : Cell → List Cell → RT
  | a, [] => spineSite a
  | a, b :: bs => .link (spineSite a) (realiseCons b bs)

def realise : (cells : List Cell) → cells ≠ [] → RT
  | [], h => False.elim (h rfl)
  | a :: as, _ => realiseCons a as

private theorem realiseCons_pair (a : Cell) (as : List Cell) (x : ℝ) :
    (realiseCons a as).pair.1.eval x = (Num.val (a :: as) x).1 ∧
    (realiseCons a as).pair.2.eval x = (Num.val (a :: as) x).2 := by
  induction as generalizing a with
  | nil =>
    obtain ⟨hs, ht⟩ := site_eval a x
    simp [realiseCons,Num.val,hs,ht]
  | cons b bs ih =>
    obtain ⟨hl,hr⟩ := site_eval a x
    obtain ⟨hz,hs⟩ := ih b
    change ((spineSite a).pair.2*(realiseCons b bs).pair.1 +
      ((spineSite a).pair.1 - (spineSite a).pair.2)*(realiseCons b bs).pair.2).eval x = _ ∧
      ((spineSite a).pair.2 * (realiseCons b bs).pair.1).eval x = _
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub,
      hl, hr, hz, hs]
    simp [Num.val]

theorem realise_eval (cells : List Cell) (h : cells ≠ []) (x : ℝ) :
    (realise cells h).pair.1.eval x = (Num.val cells x).1 := by
  cases cells with
  | nil => contradiction
  | cons a as => exact (realiseCons_pair a as x).1

theorem realise_skip_eval (cells : List Cell) (h : cells ≠ []) (x : ℝ) :
    (realise cells h).pair.2.eval x = (Num.val cells x).2 := by
  cases cells with
  | nil => contradiction
  | cons a as => exact (realiseCons_pair a as x).2

private def siteSize : Cell → ℕ
  | none => 1
  | some _ => 11

private theorem site_size (k : Cell) : (spineSite k).size = siteSize k := by
  cases k with
  | none => rfl
  | some b => cases b <;> rfl

private theorem realiseCons_size (a : Cell) (as : List Cell) :
    (realiseCons a as).size = ((a :: as).map siteSize).sum := by
  induction as generalizing a with
  | nil => simp [realiseCons,site_size]
  | cons b bs ih =>
    change (spineSite a).size + (realiseCons b bs).size = _
    rw [site_size, ih b]
    rfl

theorem family_nonempty {m j pad : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    Num.family m j pad ≠ [] := by
  intro h
  have he := congrArg List.length h
  simp [Num.family] at he
  omega

theorem realise_size {m j pad : ℕ} (hj : j ≤ m) (h : Num.family m j pad ≠ []) :
    (realise (Num.family m j pad) h).size = 11*m + pad := by
  have size_all (xs : List Cell) (hne : xs ≠ []) :
      (realise xs hne).size = (xs.map siteSize).sum := by
    cases xs with
    | nil => contradiction
    | cons a as => exact realiseCons_size a as
  rw [size_all]
  simp [Num.family,siteSize,List.sum_replicate, smul_eq_mul]
  omega

end TaskN.Antichain
