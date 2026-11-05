import Research.Backfill.Paper7.SunArmRearrangement
import Research.Backfill.Paper7.PQArmCoordinates

/-! A genuine SunV graph isomorphism for arbitrary lists with entries ≤ 2.
The lists need not be ordered and may contain any number of zeros. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Normalize
open BackfillPaper7.Challenge Paper7Cleared Paper7Reduced

def countP1 (b : ℕ) (L : Fin b → List ℕ) (k : Fin b) : ℕ := by
  let : Fintype (LengthIndex (L k) 1) :=
    inferInstanceAs (Fintype {j : Fin (L k).length // (L k).get j = 1})
  exact Fintype.card (LengthIndex (L k) 1)
#print axioms Paper7Normalize.countP1

def countP2 (b : ℕ) (L : Fin b → List ℕ) (k : Fin b) : ℕ := by
  let : Fintype (LengthIndex (L k) 2) :=
    inferInstanceAs (Fintype {j : Fin (L k).length // (L k).get j = 2})
  exact Fintype.card (LengthIndex (L k) 2)
#print axioms Paper7Normalize.countP2

def normalizedOneEquiv (b : ℕ) (L : Fin b → List ℕ) (k : Fin b) :
    LengthIndex (L k) 1 ≃ LengthIndex (pq b (countP1 b L) (countP2 b L) k) 1 := by
  let : Fintype (LengthIndex (L k) 1) :=
    inferInstanceAs (Fintype {j : Fin (L k).length // (L k).get j = 1})
  let : Fintype (LengthIndex (pq b (countP1 b L) (countP2 b L) k) 1) :=
    inferInstanceAs (Fintype (PQArmIndex b (countP1 b L) (countP2 b L) 1 k))
  apply Fintype.equivOfCardEq
  change countP1 b L k = Fintype.card (PQArmIndex b (countP1 b L) (countP2 b L) 1 k)
  exact (card_PQArmIndex_one b (countP1 b L) (countP2 b L) k).symm
#print axioms Paper7Normalize.normalizedOneEquiv

def normalizedTwoEquiv (b : ℕ) (L : Fin b → List ℕ) (k : Fin b) :
    LengthIndex (L k) 2 ≃ LengthIndex (pq b (countP1 b L) (countP2 b L) k) 2 := by
  let : Fintype (LengthIndex (L k) 2) :=
    inferInstanceAs (Fintype {j : Fin (L k).length // (L k).get j = 2})
  let : Fintype (LengthIndex (pq b (countP1 b L) (countP2 b L) k) 2) :=
    inferInstanceAs (Fintype (PQArmIndex b (countP1 b L) (countP2 b L) 2 k))
  apply Fintype.equivOfCardEq
  change countP2 b L k = Fintype.card (PQArmIndex b (countP1 b L) (countP2 b L) 2 k)
  exact (card_PQArmIndex_two b (countP1 b L) (countP2 b L) k).symm
#print axioms Paper7Normalize.normalizedTwoEquiv

def normalizedLiveEquiv (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) (k : Fin b) :
    LiveIndex (L k) ≃ LiveIndex (pq b (countP1 b L) (countP2 b L) k) :=
  liveIndexEquiv _ _ (hL k)
    (fun j => by have := pq_length_one_or_two b (countP1 b L) (countP2 b L) k j; omega)
    (normalizedOneEquiv b L k) (normalizedTwoEquiv b L k)
#print axioms Paper7Normalize.normalizedLiveEquiv

theorem normalizedLiveEquiv_length (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) (k : Fin b)
    (j : LiveIndex (L k)) :
    (pq b (countP1 b L) (countP2 b L) k).get (normalizedLiveEquiv b L hL k j).val =
      (L k).get j.val :=
  liveIndexEquiv_length _ _ _ _ _ _ j
#print axioms Paper7Normalize.normalizedLiveEquiv_length

def normalizedArmEquiv (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) (k : Fin b) :
    (Σ j : Fin (L k).length, Fin ((L k).get j)) ≃
      (Σ j : Fin (pq b (countP1 b L) (countP2 b L) k).length,
        Fin ((pq b (countP1 b L) (countP2 b L) k).get j)) :=
  armVertexEquiv _ _ (normalizedLiveEquiv b L hL k) (normalizedLiveEquiv_length b L hL k)
#print axioms Paper7Normalize.normalizedArmEquiv

theorem normalizedArmEquiv_depth (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) (k : Fin b)
    (x : Σ j : Fin (L k).length, Fin ((L k).get j)) :
    (normalizedArmEquiv b L hL k x).2.val = x.2.val := rfl
#print axioms Paper7Normalize.normalizedArmEquiv_depth

theorem normalizedArmEquiv_index_eq (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) (k : Fin b)
    (x y : Σ j : Fin (L k).length, Fin ((L k).get j)) :
    (normalizedArmEquiv b L hL k x).1 = (normalizedArmEquiv b L hL k y).1 ↔ x.1 = y.1 :=
  armVertexEquiv_index_eq _ _ _ _ x y
#print axioms Paper7Normalize.normalizedArmEquiv_index_eq

def sunNormalizeEquiv (b : ℕ) (L : Fin b → List ℕ)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) :
    SunV b L ≃ SunV b (pq b (countP1 b L) (countP2 b L)) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight (normalizedArmEquiv b L hL))
#print axioms Paper7Normalize.sunNormalizeEquiv

def sunNormalizeIso (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) :
    sunGraph b L ≃g SG b (countP1 b L) (countP2 b L) where
  toEquiv := sunNormalizeEquiv b L hL
  map_rel_iff' := by
    intro x y
    rcases x with i | ⟨k, x⟩ <;> rcases y with j | ⟨l, y⟩
    · change (SG b (countP1 b L) (countP2 b L)).Adj (Sum.inl i) (Sum.inl j) ↔ _
      rw [sun_cycle_adj_iff b _ hb, sun_cycle_adj_iff b L hb]
    · change (SG b (countP1 b L) (countP2 b L)).Adj
        (Sum.inl i) (Sum.inr ⟨l, normalizedArmEquiv b L hL l y⟩) ↔ _
      rw [sun_root_arm_adj_iff, sun_root_arm_adj_iff, normalizedArmEquiv_depth]
    · change (SG b (countP1 b L) (countP2 b L)).Adj
        (Sum.inr ⟨k, normalizedArmEquiv b L hL k x⟩) (Sum.inl j) ↔ _
      rw [sun_arm_root_adj_iff, sun_arm_root_adj_iff, normalizedArmEquiv_depth]
    · change (SG b (countP1 b L) (countP2 b L)).Adj
        (Sum.inr ⟨k, normalizedArmEquiv b L hL k x⟩)
        (Sum.inr ⟨l, normalizedArmEquiv b L hL l y⟩) ↔ _
      rw [sun_arm_adj_iff, sun_arm_adj_iff,
        normalizedArmEquiv_depth, normalizedArmEquiv_depth]
      by_cases hkl : k = l
      · subst l
        simp only [true_and, ← Fin.ext_iff, normalizedArmEquiv_index_eq]
      · simp only [hkl, false_and]
#print axioms Paper7Normalize.sunNormalizeIso

end Paper7Normalize
