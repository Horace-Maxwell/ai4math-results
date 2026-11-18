import Research.TaskH.Fan.AdjEqConnectivity

/-! Actual set retractions for connectivity; no preserved path-length claim. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

noncomputable def torsoRetraction (S : Set V) (r : S) : V → S := by
  classical
  exact fun v => if hv : v ∈ S then ⟨v, hv⟩ else r

@[simp]
theorem torsoRetraction_mem (S : Set V) (r : S) (v : V) (hv : v ∈ S) :
    torsoRetraction S r v = ⟨v, hv⟩ := by
  classical
  simp only [torsoRetraction, dite_eq_left hv]

theorem torsoRetraction_not_mem (S : Set V) (r : S) (v : V) (hv : v ∉ S) :
    torsoRetraction S r v = r := by
  classical
  simp only [torsoRetraction, dite_eq_right hv]

theorem torsoRetraction_surjective (S : Set V) (r : S) :
    Function.Surjective (torsoRetraction S r) := by
  intro v
  exact ⟨v.1, torsoRetraction_mem S r v.1 v.2⟩

noncomputable def torsoDeleteRetraction (S : Set V) (r w : S) (hw : w ≠ r) :
    {v : V // v ≠ w.1} → {v : S // v ≠ w} := by
  classical
  intro v
  refine ⟨torsoRetraction S r v.1, ?_⟩
  intro he
  by_cases hv : v.1 ∈ S
  · have hvw : v.1 = w.1 := by
      simpa only [torsoRetraction, dite_eq_left hv] using congrArg Subtype.val he
    exact v.2 hvw
  · have hrw : r = w := by
      simpa only [torsoRetraction, dite_eq_right hv] using he
    exact hw hrw.symm

theorem torsoDeleteRetraction_surjective (S : Set V) (r w : S) (hw : w ≠ r) :
    Function.Surjective (torsoDeleteRetraction S r w hw) := by
  intro v
  have hv : v.1.1 ≠ w.1 := fun he => v.2 (Subtype.ext he)
  refine ⟨⟨v.1.1, hv⟩, ?_⟩
  apply Subtype.ext
  change torsoRetraction S r v.1.1 = v.1
  exact torsoRetraction_mem S r v.1.1 v.1.2

theorem torsoRetraction_connected (A : SimpleGraph V) (S : Set V)
    (H : SimpleGraph S) (r : S)
    (hf : ∀ {a b : V}, A.Adj a b →
      torsoRetraction S r a = torsoRetraction S r b ∨
        H.Adj (torsoRetraction S r a) (torsoRetraction S r b))
    (hA : A.Connected) : H.Connected := by
  exact connected_of_surjective_adj_or_eq (torsoRetraction S r)
    (torsoRetraction_surjective S r) hf hA

theorem torsoRetraction_delete_connected (A : SimpleGraph V) (S : Set V)
    (H : SimpleGraph S) (r w : S) (hw : w ≠ r)
    (hf : ∀ {a b : V}, A.Adj a b →
      torsoRetraction S r a = torsoRetraction S r b ∨
        H.Adj (torsoRetraction S r a) (torsoRetraction S r b))
    (hA : (A.induce {v | v ≠ w.1}).Connected) :
    (H.induce {v | v ≠ w}).Connected := by
  apply connected_of_surjective_adj_or_eq (torsoDeleteRetraction S r w hw)
    (torsoDeleteRetraction_surjective S r w hw) ?_ hA
  intro a b hab
  rcases hf hab with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr he

#print axioms torsoRetraction
#print axioms torsoRetraction_mem
#print axioms torsoRetraction_not_mem
#print axioms torsoRetraction_surjective
#print axioms torsoDeleteRetraction
#print axioms torsoDeleteRetraction_surjective
#print axioms torsoRetraction_connected
#print axioms torsoRetraction_delete_connected
end TaskH.Fan
