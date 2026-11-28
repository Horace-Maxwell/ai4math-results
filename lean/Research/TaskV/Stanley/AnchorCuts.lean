import Research.TaskV.Stanley.StarBasics
import Mathlib.Tactic.FinCases

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

def binarySizes (n a : ℕ) (c : Fin 2) : ℕ := if c = 0 then a else n - a

abbrev CutOfSize {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) :=
  {s : Finset (Fin n) // s.card = a ∧
    (G.induce (s : Set (Fin n))).Connected ∧
    (G.induce ((s : Set (Fin n))ᶜ)).Connected}

def fiberSet {n k : ℕ} (f : Fin n → Fin k) (c : Fin k) : Finset (Fin n) := by
  classical exact univ.filter fun x => f x = c

@[simp] theorem mem_fiberSet {n k : ℕ} (f : Fin n → Fin k) (c : Fin k) (x : Fin n) :
    x ∈ fiberSet f c ↔ f x = c := by classical simp [fiberSet]

theorem natCard_fiberSet {n k : ℕ} (f : Fin n → Fin k) (c : Fin k) :
    Nat.card {x : Fin n // f x = c} = (fiberSet f c).card := by
  classical rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

def cutCode {n : ℕ} (s : Finset (Fin n)) (x : Fin n) : Fin 2 := if x ∈ s then 0 else 1

@[simp] theorem cutCode_zero {n : ℕ} (s : Finset (Fin n)) (x : Fin n) :
    cutCode s x = 0 ↔ x ∈ s := by by_cases h : x ∈ s <;> simp [cutCode,h]
@[simp] theorem cutCode_one {n : ℕ} (s : Finset (Fin n)) (x : Fin n) :
    cutCode s x = 1 ↔ x ∉ s := by by_cases h : x ∈ s <;> simp [cutCode,h]

theorem connectedCoefficient_two {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) :
    connectedCoefficient G 2 (binarySizes n a) = Nat.card (CutOfSize G a) := by
  classical
  unfold connectedCoefficient
  apply Nat.card_congr
  let side (f : Fin n → Fin 2) := fiberSet f 0
  have hz (f : Fin n → Fin 2) : {x | f x = 0} = (side f : Set (Fin n)) := by
    ext; simp [side]
  have ho (f : Fin n → Fin 2) : {x | f x = 1} = (side f : Set (Fin n))ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe, side, mem_fiberSet]
    omega
  have rz (s : Finset (Fin n)) : {x : Fin n | cutCode s x = 0} = (s : Set _) := by
    ext x; exact cutCode_zero s x
  have ro (s : Finset (Fin n)) : {x : Fin n | cutCode s x = 1} = (s : Set _)ᶜ := by
    ext x; exact cutCode_one s x
  refine {
    toFun := fun f => ⟨side f.1, ?_, ?_, ?_⟩
    invFun := fun s => ⟨cutCode s.1, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa [side, ← natCard_fiberSet,binarySizes] using f.2.1 0
  · rw [← hz f.1]; exact f.2.2 0
  · rw [← ho f.1]; exact f.2.2 1
  · intro c
    rw [natCard_fiberSet]
    fin_cases c
    · simpa [fiberSet,binarySizes] using s.property.1
    · have he : fiberSet (cutCode s.1) 1 = univ \ s.1 := by ext; simp
      simp [he,card_sdiff_of_subset (subset_univ _),s.property.1,binarySizes]
  · intro c
    fin_cases c
    · change (G.induce {x : Fin n | cutCode s.1 x = 0}).Connected
      rw [rz s.1]; exact s.property.2.1
    · change (G.induce {x : Fin n | cutCode s.1 x = 1}).Connected
      rw [ro s.1]; exact s.property.2.2
  · intro f
    apply Subtype.ext; funext x
    by_cases h : f.1 x = 0
    · simp [cutCode,side,h]
    · have h' : f.1 x = 1 := by omega
      simp [cutCode,side,h']
  · intro s
    apply Subtype.ext; ext x
    simp [side]

end
end StanleyContinuation
