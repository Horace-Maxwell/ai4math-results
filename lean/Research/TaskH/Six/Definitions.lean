import Research.TaskH.CycleIncidence

/-!
Shared actual-graph interfaces for the k=6 proof. These are definitions,
not assumptions in the frozen original equality-case statement. Each is to
be proved from criticality and the original modulo-six count in later modules.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u}

def ShortSixCycles (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → 6 ∣ p.length → p.length = 6

def RainbowSixCycles (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    {x : V} (p : G.Walk x x), p.IsCycle → p.length = 6 →
    ∀ a b : {z : V // z ≠ v},
      a.val ∈ p.support → b.val ∈ p.support → c a = c b → a = b

end TaskH.Six

#print axioms TaskH.Six.ShortSixCycles
#print axioms TaskH.Six.RainbowSixCycles
