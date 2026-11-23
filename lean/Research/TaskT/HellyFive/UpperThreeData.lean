import Research.TaskT.HellyFive.UpperWeights

namespace TaskT.HellyFive.UpperFive
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def unpack (a : Fin 8) : Color 3 :=
  ![(a.val : ZMod 2), ((a.val / 2 : ℕ) : ZMod 2), ((a.val / 4 : ℕ) : ZMod 2)]

def encode (x : Color 3) : Fin 8 :=
  ⟨((x 0).val + (x 1).val * 2 + (x 2).val * 4) % 8, Nat.mod_lt _ (by decide)⟩

theorem unpack_encode (x : Color 3) : unpack (encode x) = x :=
  (by decide : ∀ x : Color 3, unpack (encode x) = x) x

def boundCode (a b c d e : Fin 8) : Prop :=
  (∑ r : Color 3, capacity (indexedWeight ![unpack a,unpack b,unpack c,unpack d,unpack e] r)) ≤ 23

instance (a b c d e : Fin 8) : Decidable (boundCode a b c d e) := by unfold boundCode; infer_instance

theorem testRow : ∀ d e : Fin 8, boundCode 0 1 2 d e := by decide

end TaskT.HellyFive.UpperFive
