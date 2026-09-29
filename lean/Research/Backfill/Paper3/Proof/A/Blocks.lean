import Research.Backfill.Paper3.Proof.A.Basic

/-!
# Paper 3, Theorem A cluster: block isomorphisms and small regular graphs

* `nonempty_iso_copies_of_blocks`: if `f : V → β` has no edges between different fibres and every
  fibre induces a graph isomorphic to `H`, then `G ≅ copies |β| H`.
* Every 2-regular graph on four vertices is `K_{2,2}`; every 1-regular graph on two vertices is
  `K_{1,1}`; `C₄ ≅ K_{2,2}`; `copies 1 H ≅ H`.
* Components: a set closed under adjacency contains the component of each of its vertices, and
  induces a `d`-regular graph when `G` is `d`-regular.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

/-- `C₄ ≅ K_{2,2}`: `0, 2 ↦ inl 0, inl 1` and `1, 3 ↦ inr 0, inr 1`. -/
def cycleFourIsoKdd : cycleGraph 4 ≃g Kdd 2 where
  toFun := ![.inl 0, .inr 0, .inl 1, .inr 1]
  invFun := Sum.elim ![0, 2] ![1, 3]
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

theorem kdd_two_connected : (Kdd 2).Connected :=
  (Iso.connected_iff cycleFourIsoKdd).1 cycleGraph_connected

/-- `copies 1 H ≅ H`. -/
def copiesOneIso {W : Type*} (H : SimpleGraph W) : copies 1 H ≃g H where
  toEquiv := Equiv.uniqueProd W (Fin 1)
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    have hij : i = j := Subsingleton.elim i j
    simp [hij]

/-- **Block isomorphism.** No edges between the fibres of `f`, and every fibre induces a copy
of `H`: then `G ≅ copies |β| H`. -/
theorem nonempty_iso_copies_of_blocks {V W β : Type*} [Fintype β] (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → β) (hf : ∀ u v, G.Adj u v → f u = f v)
    (φ : ∀ b, G.induce {v | f v = b} ≃g H) :
    Nonempty (G ≃g copies (Fintype.card β) H) := by
  classical
  let e := Fintype.equivFin β
  have hφ : ∀ (b : β) (v : V) (h : f v = b), φ b ⟨v, h⟩ = φ (f v) ⟨v, rfl⟩ := by
    intro b v h
    subst h
    rfl
  let Ψ : V → Fin (Fintype.card β) × W := fun v => (e (f v), φ (f v) ⟨v, rfl⟩)
  have hinj : Function.Injective Ψ := by
    intro u v huv
    simp only [Ψ, Prod.mk.injEq] at huv
    obtain ⟨h1, h2⟩ := huv
    have hfuv : f u = f v := e.injective h1
    rw [← hφ (f v) u hfuv] at h2
    have := (φ (f v)).injective h2
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨i, w⟩
    let u := (φ (e.symm i)).symm w
    refine ⟨u.1, ?_⟩
    have hu : f u.1 = e.symm i := u.2
    simp only [Ψ, Prod.mk.injEq]
    constructor
    · rw [hu, Equiv.apply_symm_apply]
    · rw [← hφ (e.symm i) u.1 hu]
      exact (φ (e.symm i)).apply_symm_apply w
  refine ⟨⟨Equiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun {u v} => ?_⟩⟩
  show (copies (Fintype.card β) H).Adj (Ψ u) (Ψ v) ↔ G.Adj u v
  simp only [Ψ, boxProd_adj, bot_adj, false_and, false_or]
  constructor
  · rintro ⟨hadj, hi⟩
    have hfuv : f u = f v := e.injective hi
    rw [← hφ (f v) u hfuv] at hadj
    exact (φ (f v)).map_adj_iff.1 hadj
  · intro hadj
    have hfuv := hf u v hadj
    refine ⟨?_, by rw [hfuv]⟩
    rw [← hφ (f v) u hfuv]
    exact (φ (f v)).map_adj_iff.2 hadj

/-- Every 2-regular graph on four vertices is `K_{2,2}`. -/
theorem nonempty_iso_kdd_two {W : Type*} [Fintype W] (H : SimpleGraph W) [LocallyFinite H]
    (hW : Fintype.card W = 4) (hH : H.IsRegularOfDegree 2) : Nonempty (H ≃g Kdd 2) := by
  classical
  have hne : Nonempty W := by
    rw [← Fintype.card_pos_iff, hW]
    norm_num
  obtain ⟨v⟩ := hne
  have hv2 : #(H.neighborFinset v) = 2 := hH.degree_eq v
  obtain ⟨u, w, huw, hNv⟩ := card_eq_two.1 hv2
  have hvu : H.Adj v u := by
    rw [← mem_neighborFinset, hNv]
    simp
  have hvw : H.Adj v w := by
    rw [← mem_neighborFinset, hNv]
    simp
  have hvuw : v ∉ ({u, w} : Finset W) := by
    simp [hvu.ne, hvw.ne]
  have hR : #((univ : Finset W) \ {v, u, w}) = 1 := by
    have := card_sdiff_add_card_eq_card (subset_univ ({v, u, w} : Finset W))
    rw [card_univ, hW, card_insert_of_notMem hvuw, card_pair huw] at this
    omega
  obtain ⟨x, hx⟩ := card_eq_one.1 hR
  have hxmem : x ∈ (univ : Finset W) \ {v, u, w} := by
    rw [hx]
    exact mem_singleton_self x
  simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hxmem
  obtain ⟨hxv, hxu, hxw⟩ := hxmem
  have hall : ∀ z, z = v ∨ z = u ∨ z = w ∨ z = x := by
    intro z
    by_contra h
    simp only [not_or] at h
    have : z ∈ (univ : Finset W) \ {v, u, w} := by simp [h.1, h.2.1, h.2.2.1]
    rw [hx, mem_singleton] at this
    exact h.2.2.2 this
  have hvx : ¬ H.Adj v x := by
    intro h
    have : x ∈ H.neighborFinset v := by
      rw [mem_neighborFinset]
      exact h
    rw [hNv] at this
    simp [hxu, hxw] at this
  have hNx : H.neighborFinset x ⊆ {u, w} := by
    intro z hz
    rw [mem_neighborFinset] at hz
    rcases hall z with rfl | rfl | rfl | rfl
    · exact absurd hz.symm hvx
    · simp
    · simp
    · exact absurd hz H.irrefl
  have hNx' : H.neighborFinset x = {u, w} := by
    apply eq_of_subset_of_card_le hNx
    rw [card_pair huw, card_neighborFinset_eq_degree, hH.degree_eq]
  have hxu' : H.Adj x u := by
    rw [← mem_neighborFinset, hNx']
    simp
  have hxw' : H.Adj x w := by
    rw [← mem_neighborFinset, hNx']
    simp
  have hvxw : v ∉ ({x, w} : Finset W) := by
    simp [Ne.symm hxv, hvw.ne]
  have huw' : ¬ H.Adj u w := by
    intro h
    have hsub : ({v, x, w} : Finset W) ⊆ H.neighborFinset u := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rw [mem_neighborFinset]
      rcases hz with rfl | rfl | rfl
      · exact hvu.symm
      · exact hxu'.symm
      · exact h
    have := card_le_card hsub
    rw [card_neighborFinset_eq_degree, hH.degree_eq, card_insert_of_notMem hvxw,
      card_pair hxw] at this
    omega
  let g : Fin 2 ⊕ Fin 2 → W := Sum.elim ![v, x] ![u, w]
  have hinj : Function.Injective g := by
    intro p q hpq
    rcases p with (a | a) <;> rcases q with (b | b) <;> fin_cases a <;> fin_cases b <;>
      simp [g, hvu.ne, hvw.ne, huw, hxv, hxu, hxw, Ne.symm hvu.ne, Ne.symm hvw.ne, Ne.symm huw,
        Ne.symm hxv, Ne.symm hxu, Ne.symm hxw] at hpq ⊢
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [hW]⟩
  have hxv' : ¬ H.Adj x v := fun h => hvx h.symm
  have hwu' : ¬ H.Adj w u := fun h => huw' h.symm
  have hadj : ∀ p q, H.Adj (g p) (g q) ↔ (Kdd 2).Adj p q := by
    intro p q
    rcases p with (a | a) <;> rcases q with (b | b) <;> fin_cases a <;> fin_cases b <;>
      simp [g, hvu, hvw, hxu', hxw', hvx, huw', hvu.symm, hvw.symm, hxu'.symm, hxw'.symm,
        hxv', hwu']
  exact ⟨(⟨Equiv.ofBijective g hbij, fun {p q} => hadj p q⟩ : Kdd 2 ≃g H).symm⟩

/-- Every 1-regular graph on two vertices is `K_{1,1}`. -/
theorem nonempty_iso_kdd_one {W : Type*} [Fintype W] (H : SimpleGraph W) [LocallyFinite H]
    (hW : Fintype.card W = 2) (hH : H.IsRegularOfDegree 1) : Nonempty (H ≃g Kdd 1) := by
  classical
  obtain ⟨a, b, hab, huniv⟩ := card_eq_two.1 (by rw [card_univ, hW] : #(univ : Finset W) = 2)
  obtain ⟨c, hc⟩ := card_eq_one.1 (hH.degree_eq a : #(H.neighborFinset a) = 1)
  have hac : H.Adj a c := by
    rw [← mem_neighborFinset, hc]
    exact mem_singleton_self c
  have hcb : c = b := by
    have : c ∈ (univ : Finset W) := mem_univ c
    rw [huniv, mem_insert, mem_singleton] at this
    rcases this with h | h
    · rw [h] at hac
      exact absurd hac H.irrefl
    · exact h
  rw [hcb] at hac
  let g : Fin 1 ⊕ Fin 1 → W := Sum.elim (fun _ => a) (fun _ => b)
  have hinj : Function.Injective g := by
    intro p q hpq
    rcases p with (i | i) <;> rcases q with (j | j) <;>
      simp [g, hab, Ne.symm hab, Subsingleton.elim i j] at hpq ⊢
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [hW]⟩
  have hadj : ∀ p q, H.Adj (g p) (g q) ↔ (Kdd 1).Adj p q := by
    intro p q
    rcases p with (i | i) <;> rcases q with (j | j) <;> simp [g, hac, hac.symm]
  exact ⟨(⟨Equiv.ofBijective g hbij, fun {p q} => hadj p q⟩ : Kdd 1 ≃g H).symm⟩

section Components

variable {V : Type*} (G : SimpleGraph V)

/-- A set closed under adjacency contains the component of each of its vertices. -/
theorem supp_subset_of_closed {S : Set V} (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) {v : V}
    (hv : v ∈ S) : (G.connectedComponentMk v).supp ⊆ S := by
  intro w hw
  rw [ConnectedComponent.mem_supp_iff] at hw
  obtain ⟨p⟩ := ConnectedComponent.exact hw.symm
  clear hw
  induction p with
  | nil => exact hv
  | cons h p ih => exact ih (hS _ hv _ h)

/-- A closed set of a `d`-regular graph induces a `d`-regular graph. -/
theorem induce_isRegularOfDegree_of_closed {S : Set V} (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S)
    {d : ℕ} [LocallyFinite G] (hG : G.IsRegularOfDegree d) [LocallyFinite (G.induce S)] :
    (G.induce S).IsRegularOfDegree d := by
  rintro ⟨v, hv⟩
  rw [← hG.degree_eq v, ← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr
    ⟨fun w => ⟨w.1.1, w.2⟩, fun w => ⟨⟨w.1, hS v hv w.1 w.2⟩, w.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- The support of a component is closed under adjacency. -/
theorem supp_closed (c : G.ConnectedComponent) :
    ∀ x ∈ c.supp, ∀ y, G.Adj x y → y ∈ c.supp :=
  fun _ hx _ hxy => c.mem_supp_of_adj_mem_supp hx hxy

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A closed set `S` of a `d`-regular graph spans `d |S| / 2` edges. -/
theorem two_mul_edgesIn_of_closed {S : Finset V} (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) {d : ℕ}
    (hG : G.IsRegularOfDegree d) : 2 * edgesIn G S = d * #S := by
  rw [two_mul_edgesIn_eq_sum]
  have h : ∀ v ∈ S, #(S.filter (G.Adj v)) = d := by
    intro v hv
    have : S.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      rw [mem_filter, mem_neighborFinset]
      exact ⟨fun h => h.2, fun h => ⟨hS v hv w h, h⟩⟩
    rw [this, card_neighborFinset_eq_degree, hG.degree_eq]
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm]

end Components

end P3A
