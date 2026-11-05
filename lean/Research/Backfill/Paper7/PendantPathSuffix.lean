import Research.Backfill.Paper7.ChallengeV2

/-! The last three edges retain the exact original pendant-neighbor condition. -/
set_option autoImplicit false
namespace Paper7BMS
open BackfillPaper7.Challenge

def tailThreeIndex (t : ℕ) (ht : 3 ≤ t) (i : Fin 4) : Fin (t + 1) :=
  ⟨t - 3 + i.val, by omega⟩
#print axioms Paper7BMS.tailThreeIndex

theorem tailThreeIndex_injective (t : ℕ) (ht : 3 ≤ t) :
    Function.Injective (tailThreeIndex t ht) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp only [tailThreeIndex] at hv
  omega
#print axioms Paper7BMS.tailThreeIndex_injective

theorem hasPendantPath_tail_three {V : Type} (G : SimpleGraph V) (t : ℕ)
    (ht : 3 ≤ t) (h : HasPendantPath G t) : HasPendantPath G 3 := by
  obtain ⟨v, hv, hedges, hneighbors⟩ := h
  refine ⟨fun i => v (tailThreeIndex t ht i),
    hv.comp (tailThreeIndex_injective t ht), ?_, ?_⟩
  · intro i
    let k : Fin t := ⟨t - 3 + i.val, by omega⟩
    have ha := hedges k
    have hleft : k.castSucc = tailThreeIndex t ht i.castSucc := by
      apply Fin.ext
      rfl
    have hright : k.succ = tailThreeIndex t ht i.succ := by
      apply Fin.ext
      dsimp only [k, tailThreeIndex, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [hleft, hright] at ha
    exact ha
  · intro i hi w
    have hpos : 0 < (tailThreeIndex t ht i).val := by
      dsimp only [tailThreeIndex]
      omega
    rw [hneighbors (tailThreeIndex t ht i) hpos w]
    constructor
    · rintro ⟨j, hij, hw⟩
      have hjlo : t - 3 ≤ j.val := by
        dsimp only [tailThreeIndex] at hij
        omega
      let k : Fin 4 := ⟨j.val - (t - 3), by omega⟩
      have hk : tailThreeIndex t ht k = j := by
        apply Fin.ext
        dsimp only [tailThreeIndex, k]
        omega
      refine ⟨k, ?_, ?_⟩
      · dsimp only [tailThreeIndex] at hij
        dsimp only [k]
        omega
      · change w = v (tailThreeIndex t ht k)
        rw [hk]
        exact hw
    · rintro ⟨j, hij, hw⟩
      refine ⟨tailThreeIndex t ht j, ?_, hw⟩
      dsimp only [tailThreeIndex]
      omega
#print axioms Paper7BMS.hasPendantPath_tail_three

end Paper7BMS
