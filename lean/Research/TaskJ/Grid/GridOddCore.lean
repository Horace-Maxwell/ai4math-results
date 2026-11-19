import Research.TaskJ.Grid.GridOddLift
import Research.TaskJ.Grid.GridDouble

namespace Grid.OddCore

open Challenge OddLift

def Clean (ds : List ℕ) (x y : Point) : Prop := defect ds x y = 0

def Alternating (ds : List ℕ) (anchor : Point → Bool) (x y : Point) : Prop :=
  Clean ds x y ∧ anchor x ≠ anchor y

private theorem ternaryCycle : Cycle [3] (Clean [3]) [1] [2] [[1],[0],[2]] where
  order := by unfold Order; decide
  size := by decide
  first := rfl
  last := rfl
  closed := by unfold Clean; decide

def binaryAnchor (x : Point) := x.headD 0 == 1

def seed : List Point := [
  [1,1,1], [0,1,0], [1,2,1], [0,0,2], [1,1,0], [0,2,2],
  [1,0,0], [0,2,1], [1,0,1], [0,1,2], [1,2,0], [0,0,1],
  [1,2,2], [0,0,0], [1,1,2], [0,2,0], [1,0,2], [0,1,1]]

private theorem seedCycle :
    Cycle [2,3,3] (Alternating [2,3,3] binaryAnchor) [1,1,1] [0,1,1] seed where
  order := by unfold Order; decide
  size := by decide
  first := rfl
  last := rfl
  closed := by unfold Alternating Clean; decide

private theorem seed_reflected (x : Point) (hx : x ∈ vertices [2,3,3]) :
    binaryAnchor (Pad.antipode [2,3,3] x) = !binaryAnchor x := by
  obtain ⟨a,u,rfl,ha,_⟩ := Pad.vertex_cases hx
  have hv : a = 0 ∨ a = 1 := by omega
  rcases hv with rfl | rfl <;> rfl

theorem allOdd_cycles (n : ℕ) :
    let ds := List.replicate (n+1) 3
    ∃ a b p, Cycle ds (Clean ds) a b p ∧ radius ds a = 0 ∧ radius ds b = 2 := by
  induction n with
  | zero => exact ⟨[1],[2],_,ternaryCycle,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,b,p,hc,ha,hb⟩ := ih
    rw [List.replicate_succ]
    refine ⟨1::a,1::b,grow p,grow_cycle hc ?_,?_,?_⟩
    · intro x y s t hxy hst
      exact (defect_grow _ _ _ _ _ hst).trans hxy
    · exact (middle_radius _ _).trans ha
    · exact (middle_radius _ _).trans hb

theorem allOdd (n : ℕ) :
    let ds := List.replicate (n+1) 3
    ∃ p a b, Order ds p ∧ p.head? = some a ∧ p.getLast? = some b ∧
      radius ds a + radius ds b = 2 ∧ edgeLoss ds p = 0 ∧
      ∀ v ∈ p, Touches (fun x y => defect ds x y = 0) p v := by
  obtain ⟨a,b,p,h,ha,hb⟩ := allOdd_cycles n
  exact ⟨p,a,b,h.order,h.first,h.last,by rw [ha,hb,zero_add],open_clean h (fun _ _ h => h)⟩

theorem mixed_cycles (n : ℕ) :
    let ds := List.replicate n 3 ++ [2,3,3]
    ∃ a b p anchor, Cycle ds (Alternating ds anchor) a b p ∧ radius ds a = 1 ∧
      radius ds b = 1 ∧ ∀ v ∈ vertices ds, anchor (Pad.antipode ds v) = !anchor v := by
  induction n with
  | zero => exact ⟨[1,1,1],[0,1,1],seed,binaryAnchor,seedCycle,rfl,rfl,seed_reflected⟩
  | succ n ih =>
    obtain ⟨a,b,p,anchor,hc,ha,hb,hr⟩ := ih
    rw [List.replicate_succ, List.cons_append]
    refine ⟨1::a,1::b,grow p,fun x => anchor x.tail,grow_cycle hc ?_,?_,?_,?_⟩
    · intro x y s t hxy hst
      exact ⟨(defect_grow _ _ _ _ _ hst).trans hxy.1,hxy.2⟩
    · exact (middle_radius _ _).trans ha
    · exact (middle_radius _ _).trans hb
    · intro x hx
      obtain ⟨y,u,rfl,_,hu⟩ := Pad.vertex_cases hx
      exact hr u hu

theorem mixed (n : ℕ) :
    let ds := List.replicate n 3 ++ [2,3,3]
    ∃ p anchor, Double.GoodEven ds 1 p anchor := by
  obtain ⟨a,b,p,anchor,h,ha,hb,hr⟩ := mixed_cycles n
  have hc := open_clean h (fun _ _ hh => hh.1)
  refine ⟨p,anchor,h.order,?_,?_,?_,?_,hc.2,?_,hr⟩
  · intro he
    have := h.size
    simp_all
  · intro x hx
    rw [h.first] at hx
    exact (Option.some.inj hx) ▸ ha
  · intro x hx
    rw [h.last] at hx
    exact (Option.some.inj hx) ▸ hb
  · simpa using hc.1
  · exact h.closed.left_of_append.imp (fun _ _ hh => hh.2)

end Grid.OddCore
