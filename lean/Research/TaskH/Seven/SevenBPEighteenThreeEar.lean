import Research.TaskH.Seven.SevenBPEighteenHooks

/-! Four explicit actual cycles from a three-edge outside ear on C18. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def threeEarVertex (u : Fin 18 → V) (a b : V) : Sum (Fin 18) (Fin 2) → V := Sum.elim u ![b,a]

theorem threeEarVertex_injective (u : Fin 18 → V) (hu : Function.Injective u)
    (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u) (hne : b ≠ a) :
    Function.Injective (threeEarVertex u a b) := by
  have hout : ∀ k : Fin 2, threeEarVertex u a b (Sum.inr k) ∉ Set.range u := by
    intro k
    fin_cases k
    · exact hb
    · exact ha
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hu he)
    | inr j => exact False.elim (hout j ⟨i,he⟩)
  | inr i =>
    cases y with
    | inl j => exact False.elim (hout i ⟨j,he.symm⟩)
    | inr j =>
      have hij : i=j := by
        fin_cases i <;> fin_cases j <;> simp_all [threeEarVertex]
      exact congrArg Sum.inr hij

def sixteenEarWalk (G : SimpleGraph V) (f : Fin 16 → V)
    (ha : ∀ i : Fin 16, G.Adj (f i) (f (i+1))) : G.Walk (f 0) (f 0) :=
  (.cons (ha 0) (.cons (ha 1) (.cons (ha 2) (.cons (ha 3) (.cons (ha 4) (.cons (ha 5) (.cons (ha 6) (.cons (ha 7) (.cons (ha 8) (.cons (ha 9) (.cons (ha 10) (.cons (ha 11) (.cons (ha 12) (.cons (ha 13) (.cons (ha 14) (.cons (ha 15) .nil))))))))))))))))

theorem sixteenEarWalk_isCycle (G : SimpleGraph V) (f : Fin 16 → V)
    (hf : Function.Injective f) (ha : ∀ i : Fin 16, G.Adj (f i) (f (i+1))) :
    (sixteenEarWalk G f ha).IsCycle := by
  rw [sixteenEarWalk,Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons,hf.eq_iff]
  · simp [Walk.edges_cons,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk,hf.eq_iff]

theorem sixteenEarWalk_length (G : SimpleGraph V) (f : Fin 16 → V)
    (ha : ∀ i : Fin 16, G.Adj (f i) (f (i+1))) : (sixteenEarWalk G f ha).length=16 := rfl

def threeEarFiveWord : Fin 16 → Sum (Fin 18) (Fin 2) := ![Sum.inl 0,Sum.inr 0,Sum.inr 1,Sum.inl 5,Sum.inl 6,Sum.inl 7,Sum.inl 8,Sum.inl 9,Sum.inl 10,Sum.inl 11,Sum.inl 12,Sum.inl 13,Sum.inl 14,Sum.inl 15,Sum.inl 16,Sum.inl 17]

theorem threeEarFiveWord_injective : Function.Injective threeEarFiveWord := by
  unfold threeEarFiveWord Function.Injective
  decide +kernel

theorem threeEarFive_adj (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (a b : V) (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 5))
    (j : Fin 16) :
    G.Adj (threeEarVertex u a b (threeEarFiveWord j))
      (threeEarVertex u a b (threeEarFiveWord (j+1))) := by
  fin_cases j
  · exact h0
  · exact hba
  · exact hend
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
  · exact hu.2 16
  · exact hu.2 17

theorem threeEarFive_forbidden (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h16 : NoSixteenCycle G) (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u)
    (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 5)) : False := by
  let f := fun i => threeEarVertex u a b (threeEarFiveWord i)
  have hf : Function.Injective f :=
    (threeEarVertex_injective u hu.1 a b ha hb hba.ne).comp threeEarFiveWord_injective
  have hadj : ∀ i : Fin 16, G.Adj (f i) (f (i+1)) := threeEarFive_adj u hu a b h0 hba hend
  exact h16 (sixteenEarWalk G f hadj) (sixteenEarWalk_isCycle G f hf hadj)
    (sixteenEarWalk_length G f hadj)

def threeEarSevenWord : Fin 14 → Sum (Fin 18) (Fin 2) := ![Sum.inl 0,Sum.inr 0,Sum.inr 1,Sum.inl 7,Sum.inl 8,Sum.inl 9,Sum.inl 10,Sum.inl 11,Sum.inl 12,Sum.inl 13,Sum.inl 14,Sum.inl 15,Sum.inl 16,Sum.inl 17]

theorem threeEarSevenWord_injective : Function.Injective threeEarSevenWord := by
  unfold threeEarSevenWord Function.Injective
  decide +kernel

theorem threeEarSeven_adj (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (a b : V) (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 7))
    (j : Fin 14) :
    G.Adj (threeEarVertex u a b (threeEarSevenWord j))
      (threeEarVertex u a b (threeEarSevenWord (j+1))) := by
  fin_cases j
  · exact h0
  · exact hba
  · exact hend
  · exact hu.2 7
  · exact hu.2 8
  · exact hu.2 9
  · exact hu.2 10
  · exact hu.2 11
  · exact hu.2 12
  · exact hu.2 13
  · exact hu.2 14
  · exact hu.2 15
  · exact hu.2 16
  · exact hu.2 17

theorem threeEarSeven_forbidden (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u)
    (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 7)) : False := by
  let f := fun i => threeEarVertex u a b (threeEarSevenWord i)
  have hf : Function.Injective f :=
    (threeEarVertex_injective u hu.1 a b ha hb hba.ne).comp threeEarSevenWord_injective
  have hadj : ∀ i : Fin 14, G.Adj (f i) (f (i+1)) := threeEarSeven_adj u hu a b h0 hba hend
  obtain ⟨x,p,hp,hl⟩ := exists_fourteen_cycle_of_injective_adj G f hf hadj
  exact h14 p hp hl

def threeEarElevenWord : Fin 14 → Sum (Fin 18) (Fin 2) := ![Sum.inl 0,Sum.inl 1,Sum.inl 2,Sum.inl 3,Sum.inl 4,Sum.inl 5,Sum.inl 6,Sum.inl 7,Sum.inl 8,Sum.inl 9,Sum.inl 10,Sum.inl 11,Sum.inr 1,Sum.inr 0]

theorem threeEarElevenWord_injective : Function.Injective threeEarElevenWord := by
  unfold threeEarElevenWord Function.Injective
  decide +kernel

theorem threeEarEleven_adj (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (a b : V) (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 11))
    (j : Fin 14) :
    G.Adj (threeEarVertex u a b (threeEarElevenWord j))
      (threeEarVertex u a b (threeEarElevenWord (j+1))) := by
  fin_cases j
  · exact hu.2 0
  · exact hu.2 1
  · exact hu.2 2
  · exact hu.2 3
  · exact hu.2 4
  · exact hu.2 5
  · exact hu.2 6
  · exact hu.2 7
  · exact hu.2 8
  · exact hu.2 9
  · exact hu.2 10
  · exact hend.symm
  · exact hba.symm
  · exact h0.symm

theorem threeEarEleven_forbidden (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u)
    (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 11)) : False := by
  let f := fun i => threeEarVertex u a b (threeEarElevenWord i)
  have hf : Function.Injective f :=
    (threeEarVertex_injective u hu.1 a b ha hb hba.ne).comp threeEarElevenWord_injective
  have hadj : ∀ i : Fin 14, G.Adj (f i) (f (i+1)) := threeEarEleven_adj u hu a b h0 hba hend
  obtain ⟨x,p,hp,hl⟩ := exists_fourteen_cycle_of_injective_adj G f hf hadj
  exact h14 p hp hl

def threeEarThirteenWord : Fin 16 → Sum (Fin 18) (Fin 2) := ![Sum.inl 0,Sum.inl 1,Sum.inl 2,Sum.inl 3,Sum.inl 4,Sum.inl 5,Sum.inl 6,Sum.inl 7,Sum.inl 8,Sum.inl 9,Sum.inl 10,Sum.inl 11,Sum.inl 12,Sum.inl 13,Sum.inr 1,Sum.inr 0]

theorem threeEarThirteenWord_injective : Function.Injective threeEarThirteenWord := by
  unfold threeEarThirteenWord Function.Injective
  decide +kernel

theorem threeEarThirteen_adj (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (a b : V) (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 13))
    (j : Fin 16) :
    G.Adj (threeEarVertex u a b (threeEarThirteenWord j))
      (threeEarVertex u a b (threeEarThirteenWord (j+1))) := by
  fin_cases j
  · exact hu.2 0
  · exact hu.2 1
  · exact hu.2 2
  · exact hu.2 3
  · exact hu.2 4
  · exact hu.2 5
  · exact hu.2 6
  · exact hu.2 7
  · exact hu.2 8
  · exact hu.2 9
  · exact hu.2 10
  · exact hu.2 11
  · exact hu.2 12
  · exact hend.symm
  · exact hba.symm
  · exact h0.symm

theorem threeEarThirteen_forbidden (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h16 : NoSixteenCycle G) (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u)
    (h0 : G.Adj (u 0) b) (hba : G.Adj b a) (hend : G.Adj a (u 13)) : False := by
  let f := fun i => threeEarVertex u a b (threeEarThirteenWord i)
  have hf : Function.Injective f :=
    (threeEarVertex_injective u hu.1 a b ha hb hba.ne).comp threeEarThirteenWord_injective
  have hadj : ∀ i : Fin 16, G.Adj (f i) (f (i+1)) := threeEarThirteen_adj u hu a b h0 hba hend
  exact h16 (sixteenEarWalk G f hadj) (sixteenEarWalk_isCycle G f hf hadj)
    (sixteenEarWalk_length G f hadj)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.threeEarVertex
#print axioms TaskH.Seven.BP.threeEarVertex_injective
#print axioms TaskH.Seven.BP.sixteenEarWalk
#print axioms TaskH.Seven.BP.sixteenEarWalk_isCycle
#print axioms TaskH.Seven.BP.sixteenEarWalk_length
#print axioms TaskH.Seven.BP.threeEarFiveWord
#print axioms TaskH.Seven.BP.threeEarFiveWord_injective
#print axioms TaskH.Seven.BP.threeEarFive_adj
#print axioms TaskH.Seven.BP.threeEarFive_forbidden
#print axioms TaskH.Seven.BP.threeEarSevenWord
#print axioms TaskH.Seven.BP.threeEarSevenWord_injective
#print axioms TaskH.Seven.BP.threeEarSeven_adj
#print axioms TaskH.Seven.BP.threeEarSeven_forbidden
#print axioms TaskH.Seven.BP.threeEarElevenWord
#print axioms TaskH.Seven.BP.threeEarElevenWord_injective
#print axioms TaskH.Seven.BP.threeEarEleven_adj
#print axioms TaskH.Seven.BP.threeEarEleven_forbidden
#print axioms TaskH.Seven.BP.threeEarThirteenWord
#print axioms TaskH.Seven.BP.threeEarThirteenWord_injective
#print axioms TaskH.Seven.BP.threeEarThirteen_adj
#print axioms TaskH.Seven.BP.threeEarThirteen_forbidden
