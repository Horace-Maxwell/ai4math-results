import Research.WordRepTensor.Proof.WRMycielski
import Research.WordRepTensor.Proof.WRFold

/-! Internal contracts for the mixed seven-vertex window route. -/

set_option autoImplicit false

namespace WordRepTensor.TaskF.Route

open WordRepTensor.Challenge ClaudeWordRep SimpleGraph

/-- Fold the index, preserving the top/shadow/root role. -/
def foldVertex {k K : ℕ} (hk : 3 ≤ k) :
    Fin K ⊕ Fin K ⊕ Unit → Fin k ⊕ Fin k ⊕ Unit
  | .inl i => .inl (fold hk i)
  | .inr (.inl i) => .inr (.inl (fold hk i))
  | .inr (.inr u) => .inr (.inr u)

/-- The original seven labels paired with their folded copies. -/
def productWinMap {k K : ℕ} [NeZero K] (hk : 3 ≤ k) (i : Fin K) (x : Fin 7) :
    (Fin k ⊕ Fin k ⊕ Unit) × (Fin K ⊕ Fin K ⊕ Unit) :=
  (foldVertex hk (winMap i x), winMap i x)

/-- The extended local window also flips the ordinary window's colour. -/
def CommonColourCertificate : Prop :=
  flipOK 11 winExtPats winExtS0 winExtS1 winMuCol = true

/-- A single state and colour convention works for both possible local windows. -/
def CommonWindowStep : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) (w : List V) (ι : Fin 7 → V),
    Represents G w → Function.Injective ι →
    ((∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf winMuEdges x y = true) ∨
     (∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf winExtEdges x y = true)) →
    colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS1) =
      !colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS0)

/-- Each ordinary–extended product window is induced and has one of two edge lists. -/
def ProductWindowsMu : Prop :=
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k), 5 ≤ K → k ≤ K → k % 2 = 1 → K % 2 = 1 →
    ∀ i : Fin K, Function.Injective (productWinMap hk i) ∧
      ((∀ x y, (tensorProd (mu k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
        wadjOf winMuEdges x y = true) ∨
       (∀ x y, (tensorProd (mu k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
        wadjOf winExtEdges x y = true))

/-- Each extended–extended product window is induced and has one of two edge lists. -/
def ProductWindowsExt : Prop :=
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k), 5 ≤ K → k ≤ K → k % 2 = 1 → K % 2 = 1 →
    ∀ i : Fin K, Function.Injective (productWinMap hk i) ∧
      ((∀ x y, (tensorProd (muExt k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
        wadjOf winMuEdges x y = true) ∨
       (∀ x y, (tensorProd (muExt k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
        wadjOf winExtEdges x y = true))

/-- Consecutive windows use exactly the same orientation state on their shared columns. -/
def ProductStateShift : Prop :=
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k)
    (w : List ((Fin k ⊕ Fin k ⊕ Unit) × (Fin K ⊕ Fin K ⊕ Unit))) (i : Fin K),
    stateOf (orient w (productWinMap hk i) winMuEdges) winMuS1 =
      stateOf (orient w (productWinMap hk (i + 1)) winMuEdges) winMuS0

end WordRepTensor.TaskF.Route
