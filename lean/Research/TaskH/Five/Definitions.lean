import Research.TaskH.CycleIncidence

/-!
Shared actual-graph interfaces for the k=5 proof. These are definitions,
not assumptions in the frozen original equality-case statement. Each is to
be proved from criticality and the original modulo-five count in later modules.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph

variable {V : Type u}

def ShortFiveCycles (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → 5 ∣ p.length → p.length = 5

def RainbowFiveCycles (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    {x : V} (p : G.Walk x x), p.IsCycle → p.length = 5 →
    ∀ a b : {z : V // z ≠ v},
      a.val ∈ p.support → b.val ∈ p.support → c a = c b → a = b

end TaskH.Five

#print axioms TaskH.Five.ShortFiveCycles
#print axioms TaskH.Five.RainbowFiveCycles
