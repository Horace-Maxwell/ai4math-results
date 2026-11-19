import Research.TaskJ.Grid.GridSplice
import Research.TaskJ.Grid.GridOddCore

namespace Grid.Core

open Challenge

/-- The endpoint and edge contributions in doubled center coordinates. -/
def Witness (ds : List ℕ) (budget : ℤ) : Prop :=
  ∃ p a b, Order ds p ∧ p.head? = some a ∧ p.getLast? = some b ∧
    radius ds a + radius ds b + edgeLoss ds p = budget ∧ Pad.CleanIncident ds p

def evenBudget (k : ℕ) : ℤ := 2 * ((k : ℤ) + (2 : ℤ) ^ (k-1) - 1)

theorem ofGood {ds : List ℕ} {k : ℕ} {p : List Point} {anchor : Point → Bool}
    (h : Double.GoodEven ds k p anchor) : Witness ds (evenBudget k) := by
  have hf := List.head?_eq_some_head h.nonempty
  have hl := List.getLast?_eq_some_getLast h.nonempty
  exact ⟨p,_,_,h.order,hf,hl,by rw [h.headRadius _ hf,h.lastRadius _ hl,h.loss]; unfold evenBudget; ring,h.incident⟩

theorem odd (n : ℕ) : Witness (List.replicate (n+1) 3) 2 := by
  obtain ⟨p,a,b,ho,hh,hl,hr,he,hi⟩ := OddCore.allOdd n
  exact ⟨p,a,b,ho,hh,hl,by rw [hr,he,add_zero],hi⟩

private def bit (i : ℕ) (x : Point) : Bool := x[i]?.getD 0 == 1

private def two : List Point := [[0],[1]]
private def twoTwoThree : List Point :=
  [[1,1,1],[0,0,0],[1,1,2],[0,0,1],[1,1,0],[0,0,2],
   [0,1,0],[1,0,2],[0,1,1],[1,0,0],[0,1,2],[1,0,1]]
private def narrow : List Point := [[1,1],[0,0],[1,2],[0,1],[1,0],[0,2]]
private def wide : List Point :=
  [[2,1],[0,0],[2,2],[0,1],[2,0],[0,2],[3,0],[1,2],[3,1],[1,0],[3,2],[1,1]]

private theorem twoGood : Double.GoodEven [2] 1 two (bit 0) where
  order := by unfold Order; decide
  nonempty := by decide
  headRadius := by intro x hx; cases hx; rfl
  lastRadius := by intro x hx; cases hx; rfl
  loss := by decide
  incident := by unfold Touches; decide
  alternates := by decide
  reflected := by decide

private theorem twoTwoThreeGood : Double.GoodEven [2,2,3] 2 twoTwoThree (bit 1) where
  order := by unfold Order; decide
  nonempty := by decide
  headRadius := by intro x hx; cases hx; rfl
  lastRadius := by intro x hx; cases hx; rfl
  loss := by decide
  incident := by unfold Touches; decide
  alternates := by decide
  reflected := by decide

theorem planeNarrow : Witness [2,3] 4 := by
  refine ⟨narrow,[1,1],[0,2],?_,rfl,rfl,?_,?_⟩
  · unfold Order; decide
  · decide
  · unfold Pad.CleanIncident Touches; decide

theorem planeWide : Witness [4,3] 2 := by
  refine ⟨wide,[2,1],[1,1],?_,rfl,rfl,?_,?_⟩
  · unfold Order; decide
  · decide
  · unfold Pad.CleanIncident Touches; decide

private theorem iterated {ds : List ℕ} {k : ℕ} {p : List Point} {a : Point → Bool}
    (h : Double.GoodEven ds k p a) (hk : 1 ≤ k) (n : ℕ) :
    ∃ p a, Double.GoodEven (List.replicate n 2 ++ ds) (k+n) p a := by
  induction n with
  | zero => exact ⟨p,a,h⟩
  | succ n ih =>
    obtain ⟨p',a',ht⟩ := ih
    exact ⟨_,_,by simpa [List.replicate_succ,Nat.add_assoc] using ht.double (by omega)⟩

theorem allEven (n : ℕ) : Witness (List.replicate (n+1) 2) (evenBudget (n+1)) := by
  obtain ⟨p,a,h⟩ := iterated twoGood (by decide) n
  simpa [List.replicate_add,Nat.add_comm 1 n] using ofGood h

theorem oneOdd (n : ℕ) :
    Witness (List.replicate n 2 ++ [2,2,3]) (evenBudget (n+2)) := by
  obtain ⟨p,a,h⟩ := iterated twoTwoThreeGood (by decide) n
  simpa [Nat.add_comm 2 n] using ofGood h

theorem severalOdd (e q : ℕ) :
    Witness (List.replicate e 2 ++ (List.replicate q 3 ++ [2,3,3])) (evenBudget (e+1)) := by
  obtain ⟨p,a,h⟩ := OddCore.mixed q
  obtain ⟨_,_,ht⟩ := iterated h (by decide) e
  simpa [Nat.add_comm 1 e] using ofGood ht

theorem Witness.inflate {pads : Pad.Padding} {budget : ℤ} (w : Witness (Pad.inner pads) budget)
    (hw : Pad.Wide pads) (hp : PositiveSides (Pad.outer pads)) :
    ∃ q, Order (Pad.outer pads) q ∧
      2 * (pathLength q : ℤ) + budget = 2 * mass (Pad.outer pads) := by
  obtain ⟨p,a,b,ho,hh,hl,hb,hi⟩ := w
  obtain ⟨q,hq,hf,he,hc⟩ := Pad.inflate pads hw ho hi
  rw [hh] at hf
  rw [hl] at he
  have ha : a ∈ vertices (Pad.inner pads) := ho.mem_iff.mp (List.mem_of_mem_head? (by simp [hh]))
  have hbb : b ∈ vertices (Pad.inner pads) := ho.mem_iff.mp (List.mem_of_mem_getLast? (by simp [hl]))
  refine ⟨q,hq,?_⟩
  cases q with
  | nil => simp at hf
  | cons x xs =>
    have ax : x = Pad.shift pads a := Option.some.inj hf
    have bx : xs.getLastD x = Pad.shift pads b := by
      rw [List.getLast?_cons] at he
      simpa only [List.getLastD_eq_getLast?] using Option.some.inj he
    have eq := identity (Pad.outer pads) x xs
    rw [order_radius_sum hp hq, bx, Pad.radius_shift hbb, hc] at eq
    have hr : radius (Pad.outer pads) x = radius (Pad.inner pads) a := ax ▸ Pad.radius_shift ha
    rw [hr] at eq
    linarith

end Grid.Core
