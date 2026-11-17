import Research.TaskH.Seven.SevenHamiltonPerms
import Research.TaskH.Seven.SevenHeptagonWords

/-! Rooted Hamilton words are constructed from actual six-point
permutations, using Mathlib's full permutation decomposition. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def rootedHamiltonWord {Q : Finset V} (e : Q ≃ Fin 7)
    (π : Equiv.Perm (Fin 6)) (i : Fin 7) : V :=
  (e.symm (Equiv.Perm.decomposeFin.symm (0, π) i)).val

theorem rootedHamiltonWord_zero {Q : Finset V} (e : Q ≃ Fin 7)
    (π : Equiv.Perm (Fin 6)) : rootedHamiltonWord e π 0 = (e.symm 0).val := by
  simp [rootedHamiltonWord]

theorem rootedHamiltonWord_succ {Q : Finset V} (e : Q ≃ Fin 7)
    (π : Equiv.Perm (Fin 6)) (i : Fin 6) :
    rootedHamiltonWord e π i.succ = (e.symm (π i).succ).val := by
  simp [rootedHamiltonWord]

/-- Every injective actual seven-point word in Q with this root is
internally encoded by a six-point permutation. -/
theorem rootedHamiltonWord_encoding {Q : Finset V} (e : Q ≃ Fin 7)
    (f : Fin 7 → V) (hf : Function.Injective f) (hQ : ∀ i : Fin 7, f i ∈ Q)
    (hzero : f 0 = (e.symm 0).val) :
    ∃ π : Equiv.Perm (Fin 6), rootedHamiltonWord e π = f := by
  let g : Fin 7 → Fin 7 := fun i => e ⟨f i, hQ i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    exact hf (congrArg Subtype.val (e.injective hij))
  let ρ : Equiv.Perm (Fin 7) := Equiv.ofBijective g
    ⟨hginj, Finite.surjective_of_injective hginj⟩
  have hρzero : ρ 0 = 0 := by
    have hz : (⟨f 0, hQ 0⟩ : Q) = e.symm 0 := Subtype.ext hzero
    change e ⟨f 0, hQ 0⟩ = 0
    rw [hz]
    exact e.apply_symm_apply 0
  rcases hpair : Equiv.Perm.decomposeFin ρ with ⟨b, π⟩
  have hρ : Equiv.Perm.decomposeFin.symm (b, π) = ρ := by
    rw [← hpair]
    exact Equiv.Perm.decomposeFin.symm_apply_apply ρ
  have hb : b = 0 := by
    have hz := congrArg (fun τ : Equiv.Perm (Fin 7) => τ 0) hρ
    simpa only [Equiv.Perm.decomposeFin_symm_apply_zero, hρzero] using hz
  subst b
  refine ⟨π, ?_⟩
  funext i
  change (e.symm (Equiv.Perm.decomposeFin.symm (0, π) i)).val = f i
  rw [hρ]
  change (e.symm (e ⟨f i, hQ i⟩)).val = f i
  simp

/-- A real absent edge from the root forbids its other endpoint in both
endpoint positions of every actual Hamilton word. -/
theorem rootedHamiltonWord_mem_avoiding {Q : Finset V} (e : Q ≃ Fin 7)
    {u v : V} (hu : (e.symm 0).val = u) (a : Fin 6)
    (hv : (e.symm a.succ).val = v) (hnon : ¬ G.Adj u v)
    (π : Equiv.Perm (Fin 6)) (hf : IsHeptagon G (rootedHamiltonWord e π)) :
    π ∈ hamiltonAvoidingEnds 0 5 a := by
  classical
  rcases hf with ⟨_hinj, h01, _h12, _h23, _h34, _h45, _h56, h60⟩
  have hroot : rootedHamiltonWord e π 0 = u := (rootedHamiltonWord_zero e π).trans hu
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro hfirst
    have hword : rootedHamiltonWord e π 1 = v := by
      have h := rootedHamiltonWord_succ e π (0 : Fin 6)
      have hidx : (0 : Fin 6).succ = (1 : Fin 7) := by
        apply Fin.ext
        rfl
      rw [hidx, hfirst] at h
      exact h.trans hv
    exact hnon (by simpa only [hroot, hword] using h01)
  · intro hlast
    have hword : rootedHamiltonWord e π 6 = v := by
      have h := rootedHamiltonWord_succ e π (5 : Fin 6)
      have hidx : (5 : Fin 6).succ = (6 : Fin 7) := by
        apply Fin.ext
        rfl
      rw [hidx, hlast] at h
      exact h.trans hv
    exact hnon (by simpa only [hroot, hword] using h60.symm)

end TaskH.Seven

#print axioms TaskH.Seven.rootedHamiltonWord
#print axioms TaskH.Seven.rootedHamiltonWord_zero
#print axioms TaskH.Seven.rootedHamiltonWord_succ
#print axioms TaskH.Seven.rootedHamiltonWord_encoding
#print axioms TaskH.Seven.rootedHamiltonWord_mem_avoiding
