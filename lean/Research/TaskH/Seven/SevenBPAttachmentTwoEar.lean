import Research.TaskH.Seven.SevenBPChordClassification

/-! One outside point and a twelve-edge C16 arc form an actual C14.
Only a handwritten fourteen-position injective word is checked finitely. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def externalCycleVertex (u : Fin 16 → V) (z : V) : Option (Fin 16) → V
  | none => z
  | some i => u i

theorem externalCycleVertex_injective (u : Fin 16 → V) (hu : Function.Injective u)
    (z : V) (hz : z ∉ Set.range u) : Function.Injective (externalCycleVertex u z) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => exact False.elim (hz ⟨j, h.symm⟩)
  | some i =>
    cases b with
    | none => exact False.elim (hz ⟨i, h⟩)
    | some j => exact congrArg some (hu h)

def externalFourEarWord : Fin 14 → Option (Fin 16) :=
  ![some 0, none, some 4, some 5, some 6, some 7, some 8,
    some 9, some 10, some 11, some 12, some 13, some 14, some 15]

theorem externalFourEarWord_injective : Function.Injective externalFourEarWord := by
  unfold externalFourEarWord Function.Injective
  decide +kernel

theorem external_four_ear_adj (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (z : V) (h0 : G.Adj z (u 0)) (h4 : G.Adj z (u 4)) (j : Fin 14) :
    G.Adj (externalCycleVertex u z (externalFourEarWord j))
      (externalCycleVertex u z (externalFourEarWord (j + 1))) := by
  fin_cases j
  · exact h0.symm
  · exact h4
  · exact hu.2 4
  · exact hu.2 5
  · exact hu.2 6
  · exact hu.2 7
  · exact hu.2 8
  · exact hu.2 9
  · exact hu.2 10
  · exact hu.2 11
  · exact hu.2 12
  · exact hu.2 13
  · exact hu.2 14
  · exact hu.2 15

theorem outside_no_zero_four_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z : V) (hz : z ∉ Set.range u)
    (h0 : G.Adj z (u 0)) : ¬ G.Adj z (u 4) := by
  intro h4
  obtain ⟨a, p, hp, hl⟩ := exists_fourteen_cycle_of_injective_adj G
    (fun i => externalCycleVertex u z (externalFourEarWord i))
    ((externalCycleVertex_injective u hu.1 z hz).comp externalFourEarWord_injective)
    (external_four_ear_adj u hu z h0 h4)
  exact hn p hp hl

def earRotateSixteen (u : Fin 16 → V) (i : Fin 16) : Fin 16 → V :=
  fun j => u (i + j)

theorem earRotateSixteen_isCycle (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (i : Fin 16) : IsCycleSixteen G (earRotateSixteen u i) := by
  constructor
  · intro a b h
    exact add_left_cancel (hu.1 h)
  · intro j
    simpa only [earRotateSixteen, add_assoc] using hu.2 (i + j)

theorem outside_no_distance_four_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z : V) (hz : z ∉ Set.range u) (i : Fin 16)
    (hi : G.Adj z (u i)) : ¬ G.Adj z (u (i + 4)) := by
  have hzr : z ∉ Set.range (earRotateSixteen u i) := by
    rintro ⟨j, hj⟩
    exact hz ⟨i + j, hj⟩
  have h0 : G.Adj z (earRotateSixteen u i 0) := by
    simpa only [earRotateSixteen, add_zero] using hi
  exact outside_no_zero_four_hooks (earRotateSixteen u i)
    (earRotateSixteen_isCycle u hu i) hn z hzr h0

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.externalCycleVertex
#print axioms TaskH.Seven.BP.externalCycleVertex_injective
#print axioms TaskH.Seven.BP.externalFourEarWord
#print axioms TaskH.Seven.BP.externalFourEarWord_injective
#print axioms TaskH.Seven.BP.external_four_ear_adj
#print axioms TaskH.Seven.BP.outside_no_zero_four_hooks
#print axioms TaskH.Seven.BP.earRotateSixteen
#print axioms TaskH.Seven.BP.earRotateSixteen_isCycle
#print axioms TaskH.Seven.BP.outside_no_distance_four_hooks
