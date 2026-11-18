import Research.TaskH.General.CycleFlux
import Research.TaskH.General.ColorCycle
import Research.TaskH.LayerCycleSeparation

/-!
Arbitrary-color nested shifts, followed by actual unoriented cycle separation.
The forward identity needs k>=3; opposite directions require k>=4, exactly
as in the original Question2. Only Boolean structural cases are split.
The shared fixed-color module is used only for its already generic
walk-rotation and dart-constant interfaces, never for a finite-color result.
-/

set_option autoImplicit false
universe u
namespace TaskH.General.GoodCycles
open SimpleGraph
open scoped Classical
variable {k : ℕ}

/-- A single shifted successor step is an actual power of the k-rotation. -/
theorem shift_step_power (a b : Fin k) (ai bi : Bool)
    (h : shiftBit b bi = finRotate k (shiftBit a ai)) :
    b = ((finRotate k) ^ (1 + (if bi then 1 else 0) - (if ai then 1 else 0))) a := by
  have : NeZero k := a.neZero
  cases ai with
  | false =>
    cases bi with
    | false => simpa [shiftBit] using h
    | true =>
      simpa [shiftBit, pow_two, Equiv.Perm.mul_apply] using congrArg (finRotate k) h
  | true =>
    cases bi with
    | false => simpa [shiftBit] using h
    | true => simpa [shiftBit] using congrArg (finRotate k) h

/-- Below the genuine orbit length, rotation powers have distinct values. -/
theorem rotate_pow_injective_below (hk : 3 ≤ k) (a : Fin k) {e f : ℕ}
    (he : e < k) (hf : f < k)
    (hsame : ((finRotate k) ^ e) a = ((finRotate k) ^ f) a) : e = f := by
  have hle : ∀ e f : ℕ, e < k → f < k → e ≤ f →
      ((finRotate k) ^ e) a = ((finRotate k) ^ f) a → e = f := by
    intro e f _he hf hef hs
    have hsum : e + (f - e) = f := by omega
    have hfix : ((finRotate k) ^ (f - e)) a = a := by
      apply ((finRotate k) ^ e).injective
      calc
        ((finRotate k) ^ e) (((finRotate k) ^ (f - e)) a) =
            ((finRotate k) ^ (e + (f - e))) a := by
          simp only [pow_add, Equiv.Perm.mul_apply]
        _ = ((finRotate k) ^ f) a := by rw [hsum]
        _ = ((finRotate k) ^ e) a := hs.symm
    have hd := (TaskH.General.rotate_pow_fixed_iff hk a (f - e)).mp hfix
    have hz : f - e = 0 := by
      by_contra hn
      have hm : k ≤ f - e := Nat.le_of_dvd (by omega : 0 < f - e) hd
      omega
    omega
  rcases le_total e f with hef | hfe
  · exact hle e f he hf hef hsame
  · exact (hle f e hf he hfe hsame.symm).symm

/-- Nested one-step shifts preserve the band mark along every common forward step. -/
theorem nested_forward (hk : 3 ≤ k) (a b : Fin k) (ai aj bi bj : Bool)
    (ha : aj = true → ai = true) (hb : bj = true → bi = true)
    (hi : shiftBit b bi = finRotate k (shiftBit a ai))
    (hj : shiftBit b bj = finRotate k (shiftBit a aj)) :
    (ai && !aj) = (bi && !bj) := by
  let ei : ℕ := 1 + (if bi then 1 else 0) - (if ai then 1 else 0)
  let ej : ℕ := 1 + (if bj then 1 else 0) - (if aj then 1 else 0)
  have hei : ei < k := by
    cases ai <;> cases bi <;> dsimp [ei] <;> omega
  have hej : ej < k := by
    cases aj <;> cases bj <;> dsimp [ej] <;> omega
  have heq : ei = ej := rotate_pow_injective_below hk a hei hej
    ((shift_step_power a b ai bi hi).symm.trans (shift_step_power a b aj bj hj))
  clear hi hj
  cases ai <;> cases aj <;> cases bi <;> cases bj <;> simp_all [ei, ej]

/-- Opposite directions would return a color in 1, 2 or 3 steps.
The k=3 exception is real, so this lemma uses the original k>=4 range. -/
theorem nested_opposite (hk : 4 ≤ k) (a b : Fin k) (ai aj bi bj : Bool)
    (ha : aj = true → ai = true) (hb : bj = true → bi = true)
    (hi : shiftBit b bi = finRotate k (shiftBit a ai))
    (hj : shiftBit a aj = finRotate k (shiftBit b bj)) : False := by
  let ei : ℕ := 1 + (if bi then 1 else 0) - (if ai then 1 else 0)
  let ej : ℕ := 1 + (if aj then 1 else 0) - (if bj then 1 else 0)
  have hi' : b = ((finRotate k) ^ ei) a := shift_step_power a b ai bi hi
  have hj' : a = ((finRotate k) ^ ej) b := shift_step_power b a bj aj hj
  have hfix : ((finRotate k) ^ (ej + ei)) a = a := by
    calc
      ((finRotate k) ^ (ej + ei)) a =
          ((finRotate k) ^ ej) (((finRotate k) ^ ei) a) := by
        simp only [pow_add, Equiv.Perm.mul_apply]
      _ = ((finRotate k) ^ ej) b := congrArg ((finRotate k) ^ ej) hi'.symm
      _ = a := hj'.symm
  have hsmall : 0 < ej + ei ∧ ej + ei ≤ 3 := by
    clear hi hj hi' hj' hfix
    cases ai <;> cases aj <;> cases bi <;> cases bj <;> simp_all [ei, ej]
  have hd := (TaskH.General.rotate_pow_fixed_iff (by omega : 3 ≤ k) a (ej + ei)).mp hfix
  have hle : k ≤ ej + ei := Nat.le_of_dvd hsmall.1 hd
  omega

variable {V : Type u} {G : SimpleGraph V}

theorem nested_mark_constant (hk : 3 ≤ k) {x y : V} (p : G.Walk x y)
    (c : V → Fin k) (si sj : V → Bool)
    (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate k))
    (hj : Follows p (fun z => shiftBit (c z) (sj z)) (finRotate k)) :
    ∀ z ∈ p.support, (si z && !sj z) = (si x && !sj x) := by
  apply TaskH.GoodCycles.dart_constant_on_support p (fun z => si z && !sj z)
  intro d hd
  exact nested_forward hk (c d.fst) (c d.snd)
    (si d.fst) (sj d.fst) (si d.snd) (sj d.snd)
    (hsub d.fst) (hsub d.snd) (hi d hd) (hj d hd)

theorem nested_opposite_impossible (hk : 4 ≤ k) {x y : V}
    (p : G.Walk x y) (hpos : 0 < p.length) (c : V → Fin k) (si sj : V → Bool)
    (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate k))
    (hj : Follows p.reverse (fun z => shiftBit (c z) (sj z)) (finRotate k)) : False := by
  cases p with
  | nil => simp at hpos
  | @cons x y z h p =>
    have hmi : (⟨(x, y), h⟩ : G.Dart) ∈ (Walk.cons h p).darts := by
      simp [Walk.darts_cons]
    have hmj : (⟨(y, x), h.symm⟩ : G.Dart) ∈ (Walk.cons h p).reverse.darts := by
      rw [Walk.mem_darts_reverse]
      exact hmi
    exact nested_opposite hk (c x) (c y) (si x) (sj x) (si y) (sj y)
      (hsub x) (hsub y) (hi _ hmi) (hj _ hmj)

/-- Cycles obtained at different boundaries of nested layers have different
unoriented edge sets. All hypotheses refer to actual cycles and color steps. -/
theorem layer_cycle_edges_ne_of_lt [DecidableEq V] (hk : 4 ≤ k)
    (c : V → Fin k) (T : ℕ → Set V)
    (hanti : ∀ {i j : ℕ}, i ≤ j → T j ⊆ T i)
    (t : Fin (k + 1) → V) (p : ∀ i : Fin (k + 1), G.Walk (t i) (t i))
    (hp : ∀ i, (p i).IsCycle)
    (hf : ∀ i, Follows (p i)
      (fun z => shiftBit (c z) (decide (z ∈ T (i.val + 1)))) (finRotate k))
    (ht : ∀ i, t i ∈ T i.val ∧ t i ∉ T (i.val + 1))
    (i j : Fin (k + 1)) (hij : i.val < j.val) :
    (p i).edges.toFinset ≠ (p j).edges.toFinset := by
  intro heq
  let si : V → Bool := fun z => decide (z ∈ T (i.val + 1))
  let sj : V → Bool := fun z => decide (z ∈ T (j.val + 1))
  have hsub : ∀ z, sj z = true → si z = true := by
    intro z hz
    have hzmem : z ∈ T (j.val + 1) := by simpa only [sj, decide_eq_true_eq] using hz
    have hm : z ∈ T (i.val + 1) := hanti (by omega) hzmem
    simpa only [si, decide_eq_true_eq] using hm
  have hfi : Follows (p i) (fun z => shiftBit (c z) (si z)) (finRotate k) := hf i
  have htji : t j ∈ T (i.val + 1) := hanti (by omega) (ht j).1
  have htii := (ht i).2
  have htjj := (ht j).2
  obtain ⟨hmem, hq | hq⟩ :=
    CycleOrientation.cycle_eq_rotate_or_reverse_of_toFinset_eq (hp i) (hp j) heq
  · have hfjrot : Follows ((p i).rotate (t j) hmem)
        (fun z => shiftBit (c z) (sj z)) (finRotate k) := by
      rw [← hq]
      exact hf j
    have hfj := (TaskH.GoodCycles.follows_rotate_iff (p i) (t j) hmem
      (fun z => shiftBit (c z) (sj z)) (finRotate k)).mp hfjrot
    have hm := nested_mark_constant (by omega : 3 ≤ k) (p i) c si sj hsub hfi hfj (t j) hmem
    simp [si, sj, htji, htii, htjj] at hm
  · have hfjrot : Follows ((p i).rotate (t j) hmem).reverse
        (fun z => shiftBit (c z) (sj z)) (finRotate k) := by
      rw [← hq]
      exact hf j
    have hfj := (TaskH.GoodCycles.follows_rotate_reverse_iff (p i) (t j) hmem
      (fun z => shiftBit (c z) (sj z)) (finRotate k)).mp hfjrot
    exact nested_opposite_impossible hk (p i) (by have h := (hp i).three_le_length; omega)
      c si sj hsub hfi hfj

theorem layer_cycle_edgeSets_injective [DecidableEq V] (hk : 4 ≤ k)
    (c : V → Fin k) (T : ℕ → Set V)
    (hanti : ∀ {i j : ℕ}, i ≤ j → T j ⊆ T i)
    (t : Fin (k + 1) → V) (p : ∀ i : Fin (k + 1), G.Walk (t i) (t i))
    (hp : ∀ i, (p i).IsCycle)
    (hf : ∀ i, Follows (p i)
      (fun z => shiftBit (c z) (decide (z ∈ T (i.val + 1)))) (finRotate k))
    (ht : ∀ i, t i ∈ T i.val ∧ t i ∉ T (i.val + 1)) :
    Function.Injective (fun i => (p i).edges.toFinset) := by
  intro i j heq
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · exact layer_cycle_edges_ne_of_lt hk c T hanti t p hp hf ht i j h heq
  · exact layer_cycle_edges_ne_of_lt hk c T hanti t p hp hf ht j i h heq.symm


end TaskH.General.GoodCycles

#print axioms TaskH.General.GoodCycles.shift_step_power
#print axioms TaskH.General.GoodCycles.rotate_pow_injective_below
#print axioms TaskH.General.GoodCycles.nested_forward
#print axioms TaskH.General.GoodCycles.nested_opposite
#print axioms TaskH.General.GoodCycles.nested_mark_constant
#print axioms TaskH.General.GoodCycles.nested_opposite_impossible
#print axioms TaskH.General.GoodCycles.layer_cycle_edges_ne_of_lt
#print axioms TaskH.General.GoodCycles.layer_cycle_edgeSets_injective
