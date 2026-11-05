import Research.Backfill.Paper7.SunGraphAdjacency

/-! Length-preserving arm bijections, with zero-length arms removed only
because their actual vertex type is empty. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Normalize

def LengthIndex (L : List ℕ) (t : ℕ) : Type :=
  {j : Fin L.length // L.get j = t}
#print axioms Paper7Normalize.LengthIndex

def LiveIndex (L : List ℕ) : Type := {j : Fin L.length // 0 < L.get j}
#print axioms Paper7Normalize.LiveIndex

def splitLiveIndex (L : List ℕ) (hL : ∀ j : Fin L.length, L.get j ≤ 2) :
    LiveIndex L ≃ LengthIndex L 1 ⊕ LengthIndex L 2 where
  toFun j := if h : L.get j.val = 1 then Sum.inl ⟨j.val, h⟩
    else Sum.inr ⟨j.val, by have := j.property; have := hL j.val; omega⟩
  invFun x := match x with
    | Sum.inl j => ⟨j.val, by rw [j.property]; norm_num⟩
    | Sum.inr j => ⟨j.val, by rw [j.property]; norm_num⟩
  left_inv j := by
    dsimp
    split_ifs <;> rfl
  right_inv x := by
    rcases x with j | j
    · simp only [dite_eq_left j.property]
      exact congrArg (Sum.inl : LengthIndex L 1 → LengthIndex L 1 ⊕ LengthIndex L 2)
        (Subtype.ext rfl)
    · have hn : L.get j.val ≠ 1 := by rw [j.property]; norm_num
      simp only [dite_eq_right hn]
      exact congrArg (Sum.inr : LengthIndex L 2 → LengthIndex L 1 ⊕ LengthIndex L 2)
        (Subtype.ext rfl)
#print axioms Paper7Normalize.splitLiveIndex

def liveIndexEquiv (L K : List ℕ)
    (hL : ∀ j : Fin L.length, L.get j ≤ 2)
    (hK : ∀ j : Fin K.length, K.get j ≤ 2)
    (e1 : LengthIndex L 1 ≃ LengthIndex K 1)
    (e2 : LengthIndex L 2 ≃ LengthIndex K 2) : LiveIndex L ≃ LiveIndex K :=
  (splitLiveIndex L hL).trans
    ((Equiv.sumCongr e1 e2).trans (splitLiveIndex K hK).symm)
#print axioms Paper7Normalize.liveIndexEquiv

theorem liveIndexEquiv_length (L K : List ℕ)
    (hL : ∀ j : Fin L.length, L.get j ≤ 2)
    (hK : ∀ j : Fin K.length, K.get j ≤ 2)
    (e1 : LengthIndex L 1 ≃ LengthIndex K 1)
    (e2 : LengthIndex L 2 ≃ LengthIndex K 2) (j : LiveIndex L) :
    K.get (liveIndexEquiv L K hL hK e1 e2 j).val = L.get j.val := by
  change K.get ((splitLiveIndex K hK).symm
    ((Equiv.sumCongr e1 e2) (splitLiveIndex L hL j))).val = L.get j.val
  by_cases hj : L.get j.val = 1
  · have hs : splitLiveIndex L hL j = Sum.inl ⟨j.val, hj⟩ := by
      dsimp only [splitLiveIndex]
      exact dite_eq_left hj
    rw [hs]
    change K.get (e1 ⟨j.val, hj⟩).val = L.get j.val
    exact (e1 ⟨j.val, hj⟩).property.trans hj.symm
  · have hj2 : L.get j.val = 2 := by
      have := j.property
      have := hL j.val
      omega
    have hs : splitLiveIndex L hL j = Sum.inr ⟨j.val, hj2⟩ := by
      dsimp only [splitLiveIndex]
      exact dite_eq_right hj
    rw [hs]
    change K.get (e2 ⟨j.val, hj2⟩).val = L.get j.val
    exact (e2 ⟨j.val, hj2⟩).property.trans hj2.symm
#print axioms Paper7Normalize.liveIndexEquiv_length

def finLengthEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun i := ⟨i.val, by omega⟩
  invFun i := ⟨i.val, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl
#print axioms Paper7Normalize.finLengthEquiv

def liveVertexEquiv (L : List ℕ) :
    (Σ j : Fin L.length, Fin (L.get j)) ≃
      (Σ j : LiveIndex L, Fin (L.get j.val)) where
  toFun x := ⟨⟨x.1, by have := x.2.isLt; omega⟩, x.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#print axioms Paper7Normalize.liveVertexEquiv

def armVertexEquiv (L K : List ℕ) (e : LiveIndex L ≃ LiveIndex K)
    (he : ∀ j, K.get (e j).val = L.get j.val) :
    (Σ j : Fin L.length, Fin (L.get j)) ≃
      (Σ j : Fin K.length, Fin (K.get j)) :=
  (liveVertexEquiv L).trans
    ((Equiv.sigmaCongr e (fun j => finLengthEquiv (he j).symm)).trans
      (liveVertexEquiv K).symm)
#print axioms Paper7Normalize.armVertexEquiv

theorem armVertexEquiv_depth (L K : List ℕ) (e : LiveIndex L ≃ LiveIndex K)
    (he : ∀ j, K.get (e j).val = L.get j.val)
    (x : Σ j : Fin L.length, Fin (L.get j)) :
    (armVertexEquiv L K e he x).2.val = x.2.val := rfl
#print axioms Paper7Normalize.armVertexEquiv_depth

theorem armVertexEquiv_index_eq (L K : List ℕ) (e : LiveIndex L ≃ LiveIndex K)
    (he : ∀ j, K.get (e j).val = L.get j.val)
    (x y : Σ j : Fin L.length, Fin (L.get j)) :
    (armVertexEquiv L K e he x).1 = (armVertexEquiv L K e he y).1 ↔ x.1 = y.1 := by
  let a : LiveIndex L := ⟨x.1, by have := x.2.isLt; omega⟩
  let b : LiveIndex L := ⟨y.1, by have := y.2.isLt; omega⟩
  change (e a).val = (e b).val ↔ x.1 = y.1
  constructor
  · intro h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  · intro h
    have hab : a = b := Subtype.ext h
    exact congrArg (fun j => (e j).val) hab
#print axioms Paper7Normalize.armVertexEquiv_index_eq

end Paper7Normalize
