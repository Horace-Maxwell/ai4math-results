import Research.TaskH.CycleIncidence

/-!
Shared actual-graph interfaces for the k=7 proof. These are definitions,
not assumptions in the frozen original equality-case statement. Each is to
be proved from criticality and the original modulo-seven count in later modules.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

variable {V : Type u}

def ShortSevenCycles (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → 7 ∣ p.length → p.length = 7

def RainbowSevenCycles (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    {x : V} (p : G.Walk x x), p.IsCycle → p.length = 7 →
    ∀ a b : {z : V // z ≠ v},
      a.val ∈ p.support → b.val ∈ p.support → c a = c b → a = b

end TaskH.Seven

#print axioms TaskH.Seven.ShortSevenCycles
#print axioms TaskH.Seven.RainbowSevenCycles
