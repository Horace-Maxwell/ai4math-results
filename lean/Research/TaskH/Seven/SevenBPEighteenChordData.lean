import Research.TaskH.Seven.SevenBPEighteenCycle

/-! Two handwritten actual fourteen-cycle words exclude simultaneous
C18 seven-chords at step6 and nine-chords at step3. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def EighteenChordWordValid (E : Finset (Sym2 (Fin 18))) (w : Fin 14 → Fin 18) : Prop :=
  Function.Injective w ∧ ∀ j : Fin 14,
    w j + 1 = w (j + 1) ∨ w (j + 1) + 1 = w j ∨ s(w j, w (j + 1)) ∈ E

def eighteenSevenRequired : Finset (Sym2 (Fin 18)) := {s(0,7), s(6,13)}
def eighteenSevenWord : Fin 14 → Fin 18 := ![0,1,2,3,4,5,6,13,12,11,10,9,8,7]
def eighteenNineRequired : Finset (Sym2 (Fin 18)) := {s(0,9), s(3,12)}
def eighteenNineWord : Fin 14 → Fin 18 := ![0,9,8,7,6,5,4,3,12,13,14,15,16,17]

theorem eighteenSevenWord_valid : EighteenChordWordValid eighteenSevenRequired eighteenSevenWord := by
  unfold EighteenChordWordValid eighteenSevenRequired eighteenSevenWord Function.Injective
  decide +kernel

theorem eighteenNineWord_valid : EighteenChordWordValid eighteenNineRequired eighteenNineWord := by
  unfold EighteenChordWordValid eighteenNineRequired eighteenNineWord Function.Injective
  decide +kernel

theorem eighteen_adj_of_edge_eq (u : Fin 18 → V) (a b x y : Fin 18)
    (ha : G.Adj (u a) (u b)) (he : s(x,y) = s(a,b)) : G.Adj (u x) (u y) := by
  have hh : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using he
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ha
  · exact ha.symm

theorem eighteen_rotated_word_cycle (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (a : Fin 18) (E : Finset (Sym2 (Fin 18))) (w : Fin 14 → Fin 18)
    (hw : EighteenChordWordValid E w)
    (hE : ∀ i j : Fin 18, s(i,j) ∈ E → G.Adj (u (a+i)) (u (a+j))) :
    ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 14 := by
  let f : Fin 14 → V := fun i => u (a + w i)
  have hf : Function.Injective f := by
    intro i j he
    exact hw.1 (add_left_cancel (hu.1 he))
  have ha : ∀ i : Fin 14, G.Adj (f i) (f (i+1)) := by
    intro i
    change G.Adj (u (a+w i)) (u (a+w (i+1)))
    rcases hw.2 i with he | he | he
    · have hh := hu.2 (a+w i)
      simpa only [add_assoc, he] using hh
    · have hh := (hu.2 (a+w (i+1))).symm
      simpa only [add_assoc, he] using hh
    · exact hE _ _ he
  exact exists_fourteen_cycle_of_injective_adj G f hf ha

theorem eighteen_no_two_seven_chords (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (a : Fin 18)
    (h0 : G.Adj (u a) (u (a+7))) : ¬ G.Adj (u (a+6)) (u ((a+6)+7)) := by
  intro h6
  have hreq : ∀ i j : Fin 18, s(i,j) ∈ eighteenSevenRequired →
      G.Adj (u (a+i)) (u (a+j)) := by
    intro i j he
    simp only [eighteenSevenRequired, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · refine eighteen_adj_of_edge_eq u (a+0) (a+7) (a+i) (a+j) ?_ ?_
      · simpa only [add_zero] using h0
      · simpa using congrArg (Sym2.map (fun t => a+t)) he
    · refine eighteen_adj_of_edge_eq u (a+6) (a+13) (a+i) (a+j) ?_ ?_
      · simpa only [add_assoc, show (6 : Fin 18)+7=13 by decide] using h6
      · simpa using congrArg (Sym2.map (fun t => a+t)) he
  obtain ⟨x,p,hp,hl⟩ := eighteen_rotated_word_cycle u hu a _ _ eighteenSevenWord_valid hreq
  exact h14 p hp hl

theorem eighteen_no_two_nine_chords (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (a : Fin 18)
    (h0 : G.Adj (u a) (u (a+9))) : ¬ G.Adj (u (a+3)) (u ((a+3)+9)) := by
  intro h3
  have hreq : ∀ i j : Fin 18, s(i,j) ∈ eighteenNineRequired →
      G.Adj (u (a+i)) (u (a+j)) := by
    intro i j he
    simp only [eighteenNineRequired, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · refine eighteen_adj_of_edge_eq u (a+0) (a+9) (a+i) (a+j) ?_ ?_
      · simpa only [add_zero] using h0
      · simpa using congrArg (Sym2.map (fun t => a+t)) he
    · refine eighteen_adj_of_edge_eq u (a+3) (a+12) (a+i) (a+j) ?_ ?_
      · simpa only [add_assoc, show (3 : Fin 18)+9=12 by decide] using h3
      · simpa using congrArg (Sym2.map (fun t => a+t)) he
  obtain ⟨x,p,hp,hl⟩ := eighteen_rotated_word_cycle u hu a _ _ eighteenNineWord_valid hreq
  exact h14 p hp hl

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.EighteenChordWordValid
#print axioms TaskH.Seven.BP.eighteenSevenRequired
#print axioms TaskH.Seven.BP.eighteenSevenWord
#print axioms TaskH.Seven.BP.eighteenNineRequired
#print axioms TaskH.Seven.BP.eighteenNineWord
#print axioms TaskH.Seven.BP.eighteenSevenWord_valid
#print axioms TaskH.Seven.BP.eighteenNineWord_valid
#print axioms TaskH.Seven.BP.eighteen_adj_of_edge_eq
#print axioms TaskH.Seven.BP.eighteen_rotated_word_cycle
#print axioms TaskH.Seven.BP.eighteen_no_two_seven_chords
#print axioms TaskH.Seven.BP.eighteen_no_two_nine_chords
