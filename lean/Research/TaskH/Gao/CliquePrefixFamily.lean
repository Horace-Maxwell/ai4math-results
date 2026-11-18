import Research.TaskH.Gao.CliquePaths
import Research.TaskH.Gao.Challenge

/-! Set/ncard version of the actual clique-prefix construction. The positive
ncard bound derives finiteness internally; no family-existence oracle is used. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

/-- Exact lengths 1 through |K|-1 between arbitrary fixed distinct clique points. -/
theorem clique_path_length (K : Set V) (hK : G.IsClique K) (hcard : 3 ≤ K.ncard)
    (x u : V) (hx : x ∈ K) (hu : u ∈ K) (hxu : x ≠ u)
    (j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K.ncard - 1) :
    ∃ p : G.Walk x u, p.IsPath ∧ p.length = j ∧ ∀ z ∈ p.support, z ∈ K := by
  classical
  have hfinite : K.Finite := Set.finite_of_ncard_pos (by omega)
  let F : Finset V := hfinite.toFinset
  have hF : G.IsClique (F : Set V) := by
    simpa only [F, hfinite.coe_toFinset] using hK
  have hxF : x ∈ F := hfinite.mem_toFinset.mpr hx
  have huF : u ∈ F := hfinite.mem_toFinset.mpr hu
  have hFcard : F.card = K.ncard := (Set.ncard_eq_toFinset_card K hfinite).symm
  obtain ⟨p, hp, hlen, hsupp⟩ :=
    finset_clique_path_exact j F x u hF hxF huF hxu hj (by omega)
  exact ⟨p, hp, hlen, fun z hz => hfinite.mem_toFinset.mp (hsupp z hz)⟩

/-- The true Fin(|K|-1) family of lengths i+1. The target u is quantified
externally, so this theorem applies separately to every actual u in K-x. -/
theorem clique_prefix_family (K : Set V) (hK : G.IsClique K) (hcard : 3 ≤ K.ncard)
    (x u : V) (hx : x ∈ K) (hu : u ∈ K) (hxu : x ≠ u) :
    ∃ p : Fin (K.ncard - 1) → G.Walk x u,
      ∀ i, (p i).IsPath ∧ (p i).length = i.val + 1 ∧ ∀ z ∈ (p i).support, z ∈ K := by
  classical
  have hex : ∀ i : Fin (K.ncard - 1), ∃ p : G.Walk x u,
      p.IsPath ∧ p.length = i.val + 1 ∧ ∀ z ∈ p.support, z ∈ K := by
    intro i
    have hi := i.isLt
    exact clique_path_length K hK hcard x u hx hu hxu (i.val + 1) (by omega) (by omega)
  choose p hp using hex
  exact ⟨p, hp⟩

/-- Omitting the length-one member gives a genuine Gao-admissible family
of lengths 2 through |K|-1, derived from the same actual prefix family. -/
theorem clique_has_admissible_prefix (K : Set V) (hK : G.IsClique K) (hcard : 3 ≤ K.ncard)
    (x u : V) (hx : x ∈ K) (hu : u ∈ K) (hxu : x ≠ u) :
    HasAdmissiblePaths G x u (K.ncard - 2) := by
  classical
  obtain ⟨p, hp⟩ := clique_prefix_family K hK hcard x u hx hu hxu
  have hidx : ∀ i : Fin (K.ncard - 2), i.val + 1 < K.ncard - 1 := by
    intro i
    have hi := i.isLt
    omega
  refine ⟨2, 1, (fun i => p ⟨i.val + 1, hidx i⟩), by omega, Or.inl rfl, ?_⟩
  intro i
  have hpi := hp ⟨i.val + 1, hidx i⟩
  refine ⟨hpi.1, ?_⟩
  have hlen := hpi.2.1
  change (p ⟨i.val + 1, hidx i⟩).length = 2 + i.val * 1
  dsimp at hlen
  omega

#print axioms clique_path_length
#print axioms clique_prefix_family
#print axioms clique_has_admissible_prefix
end TaskH.Gao
