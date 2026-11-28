import Research.TaskV.Stanley.CoreWeights
import Research.TaskV.Stanley.StarCore
import Research.TaskV.Stanley.ChallengePeel

namespace StanleyContinuation
open Finset SimpleGraph
noncomputable section

def weightFiber {V C : Type*} [Fintype V] (f : V → C) (i : C) : Finset V := by
  classical exact univ.filter fun v => f v = i

@[simp] theorem mem_weightFiber {V C : Type*} [Fintype V] (f : V → C) (i : C) (v : V) :
    v ∈ weightFiber f i ↔ f v = i := by classical simp [weightFiber]

def WeightedBlocks {V C : Type*} [Fintype V] (J : SimpleGraph V) (w : V → ℕ) (sizes : C → ℕ) :=
  {f : V → C // ∀ i, (∑ x ∈ weightFiber f i, w x) = sizes i ∧
    (J.induce (weightFiber f i : Set V)).Connected}

instance {V C : Type*} [Fintype V] [Finite C] (J : SimpleGraph V) (w : V → ℕ) (s : C → ℕ) :
    Finite (WeightedBlocks J w s) := by unfold WeightedBlocks; infer_instance

private def OrdinaryBlocks {n k : ℕ} (G : SimpleGraph (Fin n)) (s : Fin k → ℕ) :=
  {f : Fin n → Fin k // (∀ i, Nat.card {v : Fin n // f v = i} = s i) ∧
    ∀ i, (G.induce {v : Fin n | f v = i}).Connected}

private theorem expanded_fiber {n : ℕ} {G : SimpleGraph (Fin n)} (tg : G.Connected)
    (cg : (core G).Nonempty) {C : Type*} (f : ↥(core G) → C) (i : C) :
    (expandedCoreSet tg cg (weightFiber f i) : Set (Fin n)) = {v | f (starCenter tg cg v) = i} := by
  ext v; simp

private theorem ordinary_fiber_card {n : ℕ} {G : SimpleGraph (Fin n)} (tg : G.Connected)
    (cg : (core G).Nonempty) {C : Type*} (f : ↥(core G) → C) (i : C) :
    Nat.card {v : Fin n // f (starCenter tg cg v) = i} =
      ∑ x ∈ weightFiber f i, coreWeight G x := by
  change Nat.card ↥{v : Fin n | f (starCenter tg cg v) = i} = _
  rw [← expanded_fiber tg cg f i]
  exact (Nat.card_eq_finsetCard _).trans (card_expandedCoreSet tg cg _)

private def expand_blocks {n k : ℕ} {G : SimpleGraph (Fin n)} (tg : G.Connected)
    (cg : (core G).Nonempty) {s : Fin k → ℕ}
    (f : WeightedBlocks (coreGraph G) (fun x => coreWeight G x) s) : OrdinaryBlocks G s :=
  ⟨fun x => f.val (starCenter tg cg x),fun i => (ordinary_fiber_card tg cg f.val i).trans (f.property i).1,
    fun i => by rw [← expanded_fiber tg cg f.val i, connected_of_centers]; exact (f.property i).2⟩

private def contract_blocks {n k : ℕ} {G : SimpleGraph (Fin n)} (tg : G.Connected)
    (cg : (core G).Nonempty) {s : Fin k → ℕ} (hs : ∀ i, 2 ≤ s i)
    (g : OrdinaryBlocks G s) : WeightedBlocks (coreGraph G) (fun x => coreWeight G x) s := by
  let f (x : ↥(core G)) := g.val x.val
  have hsz (i) : 2 ≤ Nat.card {v : Fin n // g.val v = i} := by rw [g.property.1]; exact hs i
  have fixed : (fun v => f (starCenter tg cg v)) = g.val :=
    funext (starCenter_agrees_in_fiber tg cg g.val hsz g.property.2)
  refine ⟨f,fun i => ⟨?_,?_⟩⟩
  · apply (ordinary_fiber_card tg cg f i).symm.trans
    change Nat.card {v : Fin n // (fun x => f (starCenter tg cg x)) v = i} = s i
    rw [fixed]; exact g.property.1 i
  · rw [← connected_of_centers tg cg, expanded_fiber tg cg f i]
    change (G.induce {v : Fin n | (fun x => f (starCenter tg cg x)) v = i}).Connected
    rw [fixed]; exact g.property.2 i

theorem coreBlock_card {n k : ℕ} {G : SimpleGraph (Fin n)} (tg : G.Connected)
    (cg : (core G).Nonempty) (s : Fin k → ℕ) (hs : ∀ i, 2 ≤ s i) :
    Nat.card (WeightedBlocks (coreGraph G) (fun x => coreWeight G x) s) = connectedCoefficient G k s := by
  apply Nat.card_congr
  change WeightedBlocks (coreGraph G) _ s ≃ OrdinaryBlocks G s
  refine {toFun := expand_blocks tg cg, invFun := contract_blocks tg cg hs,
          left_inv := ?_, right_inv := ?_}
  · intro f
    apply Subtype.ext; funext x
    exact congrArg f.val (starCenter_core tg cg x)
  · intro g
    apply Subtype.ext; funext v
    exact starCenter_agrees_in_fiber tg cg g.val
      (fun i => (hs i).trans_eq (g.property.1 i).symm) g.property.2 v

private def relabel_blocks {V C D : Type*} [Fintype V] {J : SimpleGraph V} {w : V → ℕ}
    {s : C → ℕ} (e : C ≃ D) (f : WeightedBlocks J w s) : WeightedBlocks J w (s ∘ e.symm) := by
  refine ⟨e ∘ f.val, fun i => ?_⟩
  have eq : weightFiber (e ∘ f.val) i = weightFiber f.val (e.symm i) := by
    ext v; simp only [mem_weightFiber, Function.comp_apply]; exact e.eq_symm_apply.symm
  rw [eq]; exact f.property (e.symm i)

private theorem relabel_blocks_card {V C D : Type*} [Fintype V] (J : SimpleGraph V) (w : V → ℕ)
    (s : C → ℕ) (e : C ≃ D) : Nat.card (WeightedBlocks J w s) = Nat.card (WeightedBlocks J w (s ∘ e.symm)) := by
  apply Nat.card_congr
  refine {toFun := relabel_blocks e, invFun := fun f => ⟨e.symm ∘ f.val, fun i => ?_⟩,
          left_inv := fun f => Subtype.ext (funext fun x => e.symm_apply_apply (f.val x)),
          right_inv := fun f => Subtype.ext (funext fun x => e.apply_symm_apply (f.val x))}
  have eq : weightFiber (e.symm ∘ f.val) i = weightFiber f.val (e i) := by
    ext v; simp only [mem_weightFiber, Function.comp_apply]; exact e.symm.eq_symm_apply.symm
  rw [eq]; simpa only [Function.comp_apply, e.symm_apply_apply] using f.property (e i)

theorem sameCoreBlocks_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (tg : G.IsTree) (th : H.IsTree) (cg : (core G).Nonempty) (ch : (core H).Nonempty)
    (same : SameCSF G H) {C : Type*} [Fintype C] (s : C → ℕ) (hs : ∀ i, 2 ≤ s i) :
    Nat.card (WeightedBlocks (coreGraph G) (fun x => coreWeight G x) s) =
      Nat.card (WeightedBlocks (coreGraph H) (fun x => coreWeight H x) s) := by
  let e := Fintype.equivFin C
  let q := s ∘ e.symm
  have hq : ∀ i, 2 ≤ q i := fun i => hs (e.symm i)
  exact (relabel_blocks_card (coreGraph G) _ s e).trans ((coreBlock_card tg.connected cg q hq).trans
    ((sameConnected_of_sameCSF tg th same _ q).trans ((coreBlock_card th.connected ch q hq).symm.trans
      (relabel_blocks_card (coreGraph H) _ s e).symm)))

end
end StanleyContinuation
