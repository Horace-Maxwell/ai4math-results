import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationCore

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationFamily
open SimpleGraph TriangleFreeEnumerationCore

theorem connected_of_rank {V : Type*} (G : SimpleGraph V) (r : V) (d : V → ℕ)
    (hz : ∀ v, d v = 0 → v = r)
    (hs : ∀ v, d v ≠ 0 → ∃ w, G.Adj v w ∧ d w < d v) : G.Connected := by
  have hr : ∀ k : ℕ, ∀ v, d v = k → G.Reachable v r := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      by_cases hk : k = 0
      · have he := hz v (hv.trans hk)
        subst v
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨w, hvw, hw⟩ := hs v (by omega)
        exact hvw.reachable.trans (ih (d w) (by omega) w rfl)
  have : Nonempty V := ⟨r⟩
  exact ⟨fun u v => (hr _ u rfl).trans (hr _ v rfl).symm⟩

/-- Canonical mask decoding, not a restriction of the later Finset quantifier. -/
def neighborhoodOfMask (n mask : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

abbrev repCount : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 6
  | 6 => 19
  | 7 => 59
  | _ => 0

def codes : ℕ → List ℕ
  | 1 => [0]
  | 2 => [1]
  | 3 => [3]
  | 4 => [56, 13, 45]
  | 5 => [960, 624, 101, 433, 613, 222]
  | 6 => [31744, 2213, 8715, 8469, 1648, 17953, 1118, 8286, 13074, 1520, 2661, 17957, 21158, 28822, 17965, 9829, 16320, 22181, 22189]
  | 7 => [2064384, 135461, 135317, 278677, 1052821, 135380, 135245, 409745, 135576, 278605, 49701, 67804, 1332260, 135601, 278748, 69852, 1311843, 1182245, 1069157, 271523, 1328166, 135388, 413772, 1179868, 1311970, 1098277, 135533, 279032, 147960, 135672, 37368, 1182373, 608805, 1065464, 1182436, 1329508, 52524, 1053176, 1771041, 1331301, 1132069, 312869, 540608, 81856, 1070757, 54949, 1330470, 1333347, 312995, 581805, 1327469, 706085, 54957, 101598, 815324, 608030, 317093, 813421, 1779315]
  | _ => []

def reps (n : ℕ) (i : Fin (repCount n)) : SimpleGraph (Fin n) :=
  codeGraph n ((codes n).getD i.val 0)

instance repsDecidable (n : ℕ) (i : Fin (repCount n)) : DecidableRel (reps n i).Adj :=
  inferInstanceAs (DecidableRel (codeGraph n ((codes n).getD i.val 0)).Adj)

instance repsCliqueFreeDecidable (n : ℕ) (i : Fin (repCount n)) (k : ℕ) :
    Decidable ((reps n i).CliqueFree k) := by
  unfold SimpleGraph.CliqueFree
  infer_instance

#print axioms connected_of_rank

end CodexPaper4.TriangleFreeEnumerationFamily
