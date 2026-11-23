import Research.TaskT.HellyFive.UpperWeights

namespace TaskT.HellyFive.PlanarData
open UpperFive
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def cap (f : Fin 5 → Color 2) (r : Color 2) : ℕ := capacity (indexedWeight f r)
def freq (f : Fin 5 → Color 2) (r : Color 2) : ℕ :=
  (Finset.univ.filter fun i => f i = r).card

def classification (f : Fin 5 → Color 2) : Prop :=
  (∑ r, cap f r) ≤ 12 ∨
    ((∑ r, cap f r) ≤ 13 ∧ (∀ r, 3 ≤ cap f r) ∧ (∃ r, 4 ≤ cap f r) ∧ (∀ r, freq f r ≤ 2))

instance (f : Fin 5 → Color 2) : Decidable (classification f) := by
  unfold classification
  infer_instance

def unpack (a : Fin 4) : Color 2 := ![(a.val : ZMod 2), ((a.val / 2 : ℕ) : ZMod 2)]
def pack (r : Color 2) : Fin 4 := ⟨((r 0).val + 2*(r 1).val) % 4, Nat.mod_lt _ (by decide)⟩

theorem unpack_pack : ∀ r : Color 2, unpack (pack r) = r := by decide

def row (a b c d e : Fin 4) : Prop := classification ![unpack a,unpack b,unpack c,unpack d,unpack e]

instance (a b c d e : Fin 4) : Decidable (row a b c d e) := by unfold row; infer_instance

theorem sample : ∀ d e : Fin 4, row 0 0 0 d e := by decide

end TaskT.HellyFive.PlanarData
