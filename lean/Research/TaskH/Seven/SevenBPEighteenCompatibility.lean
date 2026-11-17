import Research.TaskH.Seven.SevenBPEighteenThreeEar

/-! Actual three-ear compatibility and the unique hook forced by each
specified three-attachment type. Triple classification remains separate. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def eighteenClassIndex (q : Fin 2) (i : Fin 9) : Fin 18 := finProdFinEquiv (i,q)
def eighteenEarAllowedOffsets : Finset (Fin 9) := {0,1,4,7,8}

theorem eighteen_three_ear_index_exclusions (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u) (hba : G.Adj b a)
    (i j : Fin 18) (hi : G.Adj (u i) b) (hj : G.Adj a (u j)) :
    j≠i+5 ∧ j≠i+7 ∧ j≠i+11 ∧ j≠i+13 := by
  let v := rotateEighteen u i
  have hv := rotateEighteen_isCycle u hu i
  have hav : a ∉ Set.range v := by
    rintro ⟨k,hk⟩
    exact ha ⟨i+k,hk⟩
  have hbv : b ∉ Set.range v := by
    rintro ⟨k,hk⟩
    exact hb ⟨i+k,hk⟩
  have h0 : G.Adj (v 0) b := by simpa only [v,rotateEighteen,add_zero] using hi
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    exact threeEarFive_forbidden v hv h16 a b hav hbv h0 hba
      (by simpa only [v,rotateEighteen,he] using hj)
  · intro he
    exact threeEarSeven_forbidden v hv h14 a b hav hbv h0 hba
      (by simpa only [v,rotateEighteen,he] using hj)
  · intro he
    exact threeEarEleven_forbidden v hv h14 a b hav hbv h0 hba
      (by simpa only [v,rotateEighteen,he] using hj)
  · intro he
    exact threeEarThirteen_forbidden v hv h16 a b hav hbv h0 hba
      (by simpa only [v,rotateEighteen,he] using hj)

theorem eighteen_three_ear_class_compatibility (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u) (hba : G.Adj b a)
    (i j : Fin 9) (hi : G.Adj (u (eighteenClassIndex 0 i)) b)
    (hj : G.Adj a (u (eighteenClassIndex 1 j))) :
    j-i ∈ eighteenEarAllowedOffsets := by
  have he := eighteen_three_ear_index_exclusions u hu h14 h16 a b ha hb hba
    (eighteenClassIndex 0 i) (eighteenClassIndex 1 j) hi hj
  have tab : ∀ i j : Fin 9,
      eighteenClassIndex 1 j ≠ eighteenClassIndex 0 i+5 →
      eighteenClassIndex 1 j ≠ eighteenClassIndex 0 i+7 →
      eighteenClassIndex 1 j ≠ eighteenClassIndex 0 i+11 →
      eighteenClassIndex 1 j ≠ eighteenClassIndex 0 i+13 →
      j-i ∈ eighteenEarAllowedOffsets := by
    unfold eighteenEarAllowedOffsets
    decide +kernel
  exact tab i j he.1 he.2.1 he.2.2.1 he.2.2.2

theorem eighteen_even_triple_forces_unique_odd_hook (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u) (hba : G.Adj b a)
    (i j : Fin 9)
    (h0 : G.Adj (u (eighteenClassIndex 0 i)) b)
    (h1 : G.Adj (u (eighteenClassIndex 0 (i+1))) b)
    (h5 : G.Adj (u (eighteenClassIndex 0 (i+5))) b)
    (hj : G.Adj a (u (eighteenClassIndex 1 j))) : j=i := by
  have hc0 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba i j h0 hj
  have hc1 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba (i+1) j h1 hj
  have hc5 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba (i+5) j h5 hj
  have tab : ∀ i j : Fin 9, j-i ∈ eighteenEarAllowedOffsets →
      j-(i+1) ∈ eighteenEarAllowedOffsets → j-(i+5) ∈ eighteenEarAllowedOffsets → j=i := by
    unfold eighteenEarAllowedOffsets
    decide +kernel
  exact tab i j hc0 hc1 hc5

theorem eighteen_odd_triple_forces_unique_even_hook (u : Fin 18 → V) (hu : IsCycleEighteen G u)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (a b : V) (ha : a ∉ Set.range u) (hb : b ∉ Set.range u) (hba : G.Adj b a)
    (i j : Fin 9) (hi : G.Adj (u (eighteenClassIndex 0 i)) b)
    (h0 : G.Adj a (u (eighteenClassIndex 1 j)))
    (h1 : G.Adj a (u (eighteenClassIndex 1 (j+1))))
    (h5 : G.Adj a (u (eighteenClassIndex 1 (j+5)))) : i=j+1 := by
  have hc0 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba i j hi h0
  have hc1 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba i (j+1) hi h1
  have hc5 := eighteen_three_ear_class_compatibility u hu h14 h16 a b ha hb hba i (j+5) hi h5
  have tab : ∀ i j : Fin 9, j-i ∈ eighteenEarAllowedOffsets →
      (j+1)-i ∈ eighteenEarAllowedOffsets → (j+5)-i ∈ eighteenEarAllowedOffsets → i=j+1 := by
    unfold eighteenEarAllowedOffsets
    decide +kernel
  exact tab i j hc0 hc1 hc5

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteenClassIndex
#print axioms TaskH.Seven.BP.eighteenEarAllowedOffsets
#print axioms TaskH.Seven.BP.eighteen_three_ear_index_exclusions
#print axioms TaskH.Seven.BP.eighteen_three_ear_class_compatibility
#print axioms TaskH.Seven.BP.eighteen_even_triple_forces_unique_odd_hook
#print axioms TaskH.Seven.BP.eighteen_odd_triple_forces_unique_even_hook
