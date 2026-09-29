import Research.Backfill.Paper3.Proof.Small.Cubic

/-!
# Labelled cubic graphs on six vertices (`LabelledCounts`)

The map `c ↦ maskGraph 6 c` is a bijection from the edge masks `c < 2^15` onto the graphs on
`Fin 6`; it carries the cubic masks (counted by the kernel in `Research.Backfill.Paper3.Proof.Small.Enum`) onto the cubic
graphs.
-/

set_option autoImplicit false

namespace P3Small

open Finset SimpleGraph BackfillPaper3.Challenge

/-- Counting graphs on `Fin 6` with a property that is read off the edge mask by `regB 6 · 3`:
`c ↦ maskGraph 6 c` is a bijection from the masks `c < 2^15` with `regB 6 c 3` onto them. -/
theorem card_regular6 (P : SimpleGraph (Fin 6) → Prop)
    (hP : ∀ c, P (maskGraph 6 c) ↔ regB 6 c 3 = true) :
    Nat.card {G : SimpleGraph (Fin 6) // P G} = 70 := by
  have h15 : (32768 : ℕ) = 2 ^ 15 := by norm_num
  let f : {c : Fin 32768 // regB 6 c.val 3 = true} → {G : SimpleGraph (Fin 6) // P G} :=
    fun c => ⟨maskGraph 6 c.1.val, (hP c.1.val).mpr c.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h' : maskGraph 6 a.1.val = maskGraph 6 b.1.val := congrArg Subtype.val h
      exact Subtype.ext (Fin.ext (maskGraph6_inj (lt_of_lt_of_eq a.1.isLt h15)
        (lt_of_lt_of_eq b.1.isLt h15) h'))
    · rintro ⟨G, hG⟩
      obtain ⟨c, hc, hadj⟩ := exists_mask6 G
      have hGc : maskGraph 6 c = G :=
        SimpleGraph.ext (funext fun i => funext fun j => propext (hadj i j).symm)
      have hPc : P (maskGraph 6 c) := by rw [hGc]; exact hG
      exact ⟨⟨⟨c, lt_of_lt_of_eq hc h15.symm⟩, (hP c).mp hPc⟩, Subtype.ext hGc⟩
  have h2 : Nat.card {c : Fin 32768 // regB 6 c.val 3 = true} =
      #((univ : Finset (Fin 32768)).filter fun c => regB 6 c.val 3 = true) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h3 : #((univ : Finset (Fin 32768)).filter fun c => regB 6 c.val 3 = true) =
      #((range 32768).filter fun c => regB 6 c 3 = true) :=
    card_filter_fin 32768 (fun c => regB 6 c 3)
  have h4 : #((range 32768).filter fun c => regB 6 c 3 = true) =
      countB 32768 (fun c => regB 6 c 3) :=
    (countB_eq_card 32768 (fun c => regB 6 c 3)).symm
  exact (Nat.card_eq_of_bijective f hf).symm.trans (h2.trans (h3.trans (h4.trans countB_cubic6)))

/-- §8: there are `70` cubic graphs on six labelled vertices. -/
theorem labelledCounts : LabelledCounts := by
  unfold LabelledCounts
  exact card_regular6 _ fun c => isRegular_maskGraph_iff 6 c 3

end P3Small
