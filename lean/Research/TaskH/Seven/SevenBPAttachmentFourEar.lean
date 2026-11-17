import Research.TaskH.Seven.SevenBPCycleAttachments

/-! Actual three- and four-edge ears between distinct C16 vertices.
The displayed words contain the real outside vertices and are injective.
Only their fixed position identities are checked finitely. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def threeExternalVertex (u : Fin 16 → V) (e : Fin 3 → V) :
    Sum (Fin 16) (Fin 3) → V
  | .inl i => u i
  | .inr j => e j

theorem threeExternalVertex_injective (u : Fin 16 → V)
    (hu : Function.Injective u) (e : Fin 3 → V) (he : Function.Injective e)
    (hx : ∀ j : Fin 3, e j ∉ Set.range u) :
    Function.Injective (threeExternalVertex u e) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (hu hab)
    | inr j => exact False.elim (hx j ⟨i, hab⟩)
  | inr i =>
    cases b with
    | inl j => exact False.elim (hx i ⟨j, hab.symm⟩)
    | inr j => exact congrArg Sum.inr (he hab)

def sharedSixEarWord : Fin 14 → Sum (Fin 16) (Fin 3) :=
  ![.inl 0, .inr 0, .inr 1, .inr 2, .inl 6, .inl 7, .inl 8,
    .inl 9, .inl 10, .inl 11, .inl 12, .inl 13, .inl 14, .inl 15]

theorem sharedSixEarWord_injective : Function.Injective sharedSixEarWord := by
  unfold sharedSixEarWord Function.Injective
  decide +kernel

theorem shared_six_ear_adj (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (e : Fin 3 → V) (h0 : G.Adj (u 0) (e 0))
    (h01 : G.Adj (e 0) (e 1)) (h12 : G.Adj (e 1) (e 2))
    (h6 : G.Adj (e 2) (u 6)) (j : Fin 14) :
    G.Adj (threeExternalVertex u e (sharedSixEarWord j))
      (threeExternalVertex u e (sharedSixEarWord (j + 1))) := by
  fin_cases j
  · exact h0
  · exact h01
  · exact h12
  · exact h6
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

theorem no_shared_zero_six_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q w : V)
    (hz : z ∉ Set.range u) (hq : q ∉ Set.range u) (hw : w ∉ Set.range u)
    (hzw : z ≠ w) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (h0 : G.Adj z (u 0)) : ¬ G.Adj w (u 6) := by
  intro h6
  let e : Fin 3 → V := ![z, q, w]
  have he : Function.Injective e := by
    have hzqn := hzq.ne
    have hqwn := hqw.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have hx : ∀ j : Fin 3, e j ∉ Set.range u := by
    intro j
    fin_cases j
    · exact hz
    · exact hq
    · exact hw
  obtain ⟨a, p, hp, hl⟩ := exists_fourteen_cycle_of_injective_adj G
    (fun i => threeExternalVertex u e (sharedSixEarWord i))
    ((threeExternalVertex_injective u hu.1 e he hx).comp sharedSixEarWord_injective)
    (shared_six_ear_adj u hu e h0.symm hzq hqw h6)
  exact hn p hp hl

theorem no_shared_distance_six_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q w : V)
    (hz : z ∉ Set.range u) (hq : q ∉ Set.range u) (hw : w ∉ Set.range u)
    (hzw : z ≠ w) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (i : Fin 16) (hi : G.Adj z (u i)) : ¬ G.Adj w (u (i + 6)) := by
  have hr : ∀ x : V, x ∉ Set.range u → x ∉ Set.range (earRotateSixteen u i) := by
    intro x hx
    rintro ⟨j, hj⟩
    exact hx ⟨i + j, hj⟩
  have h0 : G.Adj z (earRotateSixteen u i 0) := by
    simpa only [earRotateSixteen, add_zero] using hi
  exact no_shared_zero_six_hooks (earRotateSixteen u i)
    (earRotateSixteen_isCycle u hu i) hn z q w
    (hr z hz) (hr q hq) (hr w hw) hzw hzq hqw h0

theorem no_shared_distance_ten_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q w : V)
    (hz : z ∉ Set.range u) (hq : q ∉ Set.range u) (hw : w ∉ Set.range u)
    (hzw : z ≠ w) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (i : Fin 16) (hi : G.Adj z (u i)) : ¬ G.Adj w (u (i + 10)) := by
  intro hj
  have hc : (i + 10) + 6 = i := by
    have tab : ∀ k : Fin 16, (k + 10) + 6 = k := by decide +kernel
    exact tab i
  have hh := no_shared_distance_six_hooks u hu hn w q z
    hw hq hz hzw.symm hqw.symm hzq.symm (i + 10) hj
  rw [hc] at hh
  exact hh hi

def adjacentFiveEarWord : Fin 14 → Sum (Fin 16) (Fin 3) :=
  ![.inl 0, .inr 0, .inr 1, .inl 5, .inl 6, .inl 7, .inl 8,
    .inl 9, .inl 10, .inl 11, .inl 12, .inl 13, .inl 14, .inl 15]

theorem adjacentFiveEarWord_injective : Function.Injective adjacentFiveEarWord := by
  unfold adjacentFiveEarWord Function.Injective
  decide +kernel

theorem adjacent_five_ear_adj (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (e : Fin 3 → V) (h0 : G.Adj (u 0) (e 0))
    (h01 : G.Adj (e 0) (e 1)) (h5 : G.Adj (e 1) (u 5)) (j : Fin 14) :
    G.Adj (threeExternalVertex u e (adjacentFiveEarWord j))
      (threeExternalVertex u e (adjacentFiveEarWord (j + 1))) := by
  fin_cases j
  · exact h0
  · exact h01
  · exact h5
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

theorem no_adjacent_zero_five_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q : V)
    (hz : z ∉ Set.range u) (hq : q ∉ Set.range u) (hzq : G.Adj z q)
    (h0 : G.Adj z (u 0)) : ¬ G.Adj q (u 5) := by
  intro h5
  let f : Fin 2 → V := ![z, q]
  let v : Sum (Fin 16) (Fin 2) → V := Sum.elim u f
  let word : Fin 14 → Sum (Fin 16) (Fin 2) :=
    ![.inl 0, .inr 0, .inr 1, .inl 5, .inl 6, .inl 7, .inl 8,
      .inl 9, .inl 10, .inl 11, .inl 12, .inl 13, .inl 14, .inl 15]
  have hf : Function.Injective f := by
    have hzqn := hzq.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hv : Function.Injective v := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hu.1 hab)
      | inr j =>
        fin_cases j
        · exact False.elim (hz ⟨i, hab⟩)
        · exact False.elim (hq ⟨i, hab⟩)
    | inr i =>
      cases b with
      | inl j =>
        fin_cases i
        · exact False.elim (hz ⟨j, hab.symm⟩)
        · exact False.elim (hq ⟨j, hab.symm⟩)
      | inr j => exact congrArg Sum.inr (hf hab)
  have hw : Function.Injective word := by
    unfold word Function.Injective
    decide +kernel
  have ha : ∀ j : Fin 14, G.Adj (v (word j)) (v (word (j + 1))) := by
    intro j
    fin_cases j
    · exact h0.symm
    · exact hzq
    · exact h5
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
  obtain ⟨a, p, hp, hl⟩ := exists_fourteen_cycle_of_injective_adj G
    (fun i => v (word i)) (hv.comp hw) ha
  exact hn p hp hl

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.threeExternalVertex
#print axioms TaskH.Seven.BP.threeExternalVertex_injective
#print axioms TaskH.Seven.BP.sharedSixEarWord
#print axioms TaskH.Seven.BP.sharedSixEarWord_injective
#print axioms TaskH.Seven.BP.shared_six_ear_adj
#print axioms TaskH.Seven.BP.no_shared_zero_six_hooks
#print axioms TaskH.Seven.BP.no_shared_distance_six_hooks
#print axioms TaskH.Seven.BP.no_shared_distance_ten_hooks
#print axioms TaskH.Seven.BP.adjacentFiveEarWord
#print axioms TaskH.Seven.BP.adjacentFiveEarWord_injective
#print axioms TaskH.Seven.BP.adjacent_five_ear_adj
#print axioms TaskH.Seven.BP.no_adjacent_zero_five_hooks
