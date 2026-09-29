import Research.Backfill.Paper3.Proof.SSSZ.Cut
import Research.Backfill.Paper3.Challenge

/-!
# The swapping inequality `P_G(q)² ≤ P_{G × K₂}(q)` for `0 ≤ q ≤ 1`

`P_{G × K₂}(q)` is written as `∑_{A,B} q^{e(A,B)}`, where `e(A,B) = ∑_{e ∈ E(G)} ψ_{A,B}(e)` counts
the ordered adjacent pairs `(u, v)` with `u ∈ A`, `v ∈ B` (`sum_psi`). Pairs `(A, B)` are
reindexed by `C = A ∩ B`, `M = A Δ B`, `X = A \ B`; for fixed `(C, M)` an edge inside `M` has
weight `q^{[not cut by X]}` in `P_G(q)²` and `q^{[cut by X]}` in `P_{G×K₂}(q)`, and every other
edge has the same weight in both, independent of `X`. The cut lemma finishes the proof.
-/

set_option autoImplicit false

open Finset BackfillPaper3.Challenge

namespace P3SSSZ

section Swap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of orientations `(u, v)` of `e` with `u ∈ A` and `v ∈ B`. -/
def psi (A B : Finset V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => (if u ∈ A ∧ v ∈ B then 1 else 0) + (if v ∈ A ∧ u ∈ B then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

omit [Fintype V] in
@[simp] theorem psi_mk (A B : Finset V) (u v : V) :
    psi A B s(u, v) = (if u ∈ A ∧ v ∈ B then 1 else 0) + (if v ∈ A ∧ u ∈ B then 1 else 0) :=
  rfl

/-- The exponent of `q` contributed by `e` to `q^{e(A) + e(B)}`. -/
def phiG (A B : Finset V) (e : Sym2 V) : ℕ :=
  (if e ∈ A.sym2 then 1 else 0) + (if e ∈ B.sym2 then 1 else 0)

/-- Reindexing pairs `(A, B)` by `C = A ∩ B`, `M = A Δ B` and `X = A \ B`. -/
theorem sum_pairs_reindex {β : Type*} [AddCommMonoid β] (f : Finset V → Finset V → β) :
    ∑ A : Finset V, ∑ B : Finset V, f A B =
      ∑ C : Finset V, ∑ M ∈ Cᶜ.powerset, ∑ X ∈ M.powerset, f (C ∪ X) (C ∪ (M \ X)) := by
  set r1 : Finset (Finset V × Finset V) := univ.filter fun p => p.2 ⊆ p.1ᶜ with hr1
  set r2 : Finset ((Finset V × Finset V) × Finset V) :=
    univ.filter fun t => t.1.2 ⊆ t.1.1ᶜ ∧ t.2 ⊆ t.1.2 with hr2
  have e1 : ∑ C : Finset V, ∑ M ∈ Cᶜ.powerset, ∑ X ∈ M.powerset, f (C ∪ X) (C ∪ (M \ X)) =
      ∑ p ∈ r1, ∑ X ∈ p.2.powerset, f (p.1 ∪ X) (p.1 ∪ (p.2 \ X)) :=
    (sum_finset_product' r1 univ (fun C => Cᶜ.powerset) (by intro p; simp [hr1])
      (f := fun C M => ∑ X ∈ M.powerset, f (C ∪ X) (C ∪ (M \ X)))).symm
  have e2 : ∑ p ∈ r1, ∑ X ∈ p.2.powerset, f (p.1 ∪ X) (p.1 ∪ (p.2 \ X)) =
      ∑ t ∈ r2, f (t.1.1 ∪ t.2) (t.1.1 ∪ (t.1.2 \ t.2)) :=
    (sum_finset_product' r2 r1 (fun p => p.2.powerset) (by intro t; simp [hr1, hr2])
      (f := fun p X => f (p.1 ∪ X) (p.1 ∪ (p.2 \ X)))).symm
  rw [e1, e2, ← Fintype.sum_prod_type']
  symm
  apply sum_nbij' (fun t => (t.1.1 ∪ t.2, t.1.1 ∪ (t.1.2 \ t.2)))
    (fun p => ((p.1 ∩ p.2, (p.1 ∪ p.2) \ (p.1 ∩ p.2)), p.1 \ p.2))
  · intro t _
    exact mem_univ _
  · intro p _
    simp only [hr2, mem_filter, mem_univ, true_and]
    constructor
    · intro x hx
      simp only [mem_sdiff, mem_union, mem_inter, mem_compl] at hx ⊢
      tauto
    · intro x hx
      simp only [mem_sdiff, mem_union, mem_inter] at hx ⊢
      tauto
  · rintro ⟨⟨C, M⟩, X⟩ ht
    simp only [hr2, mem_filter, mem_univ, true_and] at ht
    obtain ⟨hMC, hXM⟩ := ht
    have h1 : ∀ x, x ∈ M → x ∉ C := fun x hx => mem_compl.mp (hMC hx)
    have h2 : ∀ x, x ∈ X → x ∈ M := fun x hx => hXM hx
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · ext x
      have := h1 x
      have := h2 x
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
    · ext x
      have := h1 x
      have := h2 x
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
    · ext x
      have := h1 x
      have := h2 x
      simp only [mem_sdiff, mem_union]
      tauto
  · rintro ⟨A, B⟩ _
    refine Prod.ext ?_ ?_
    · ext x
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
    · ext x
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
  · intro t _
    rfl

section Edge

variable {C M X : Finset V} (hMC : M ⊆ Cᶜ) (hXM : X ⊆ M)
include hMC hXM

omit hXM in
theorem phiG_inside {e : Sym2 V} (he : e ∈ M.sym2) :
    phiG (C ∪ X) (C ∪ (M \ X)) e = if cut X e = true then 0 else 1 := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mk_mem_sym2_iff] at he
    have hu := mem_compl.mp (hMC he.1)
    have hv := mem_compl.mp (hMC he.2)
    unfold phiG
    simp only [mk_mem_sym2_iff, mem_union, mem_sdiff, cut_mk]
    by_cases hux : u ∈ X <;> by_cases hvx : v ∈ X <;> simp [hu, hv, hux, hvx, he.1, he.2]

omit hXM in
theorem psi_inside {e : Sym2 V} (he : e ∈ M.sym2) :
    psi (C ∪ X) (C ∪ (M \ X)) e = if cut X e = true then 1 else 0 := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mk_mem_sym2_iff] at he
    have hu := mem_compl.mp (hMC he.1)
    have hv := mem_compl.mp (hMC he.2)
    simp only [psi_mk, mem_union, mem_sdiff, cut_mk]
    by_cases hux : u ∈ X <;> by_cases hvx : v ∈ X <;> simp [hu, hv, hux, hvx, he.1, he.2]

theorem phiG_outside {e : Sym2 V} (he : e ∉ M.sym2) :
    phiG (C ∪ X) (C ∪ (M \ X)) e = psi C (C ∪ M) e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mk_mem_sym2_iff] at he
    have hu1 : u ∈ M → u ∉ C := fun h => mem_compl.mp (hMC h)
    have hv1 : v ∈ M → v ∉ C := fun h => mem_compl.mp (hMC h)
    have hu2 : u ∈ X → u ∈ M := fun h => hXM h
    have hv2 : v ∈ X → v ∈ M := fun h => hXM h
    unfold phiG
    simp only [mk_mem_sym2_iff, mem_union, mem_sdiff, psi_mk]
    by_cases huC : u ∈ C <;> by_cases huM : u ∈ M <;> by_cases huX : u ∈ X <;>
      by_cases hvC : v ∈ C <;> by_cases hvM : v ∈ M <;> by_cases hvX : v ∈ X <;>
      simp_all

theorem psi_outside {e : Sym2 V} (he : e ∉ M.sym2) :
    psi (C ∪ X) (C ∪ (M \ X)) e = psi C (C ∪ M) e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mk_mem_sym2_iff] at he
    have hu1 : u ∈ M → u ∉ C := fun h => mem_compl.mp (hMC h)
    have hv1 : v ∈ M → v ∉ C := fun h => mem_compl.mp (hMC h)
    have hu2 : u ∈ X → u ∈ M := fun h => hXM h
    have hv2 : v ∈ X → v ∈ M := fun h => hXM h
    simp only [mem_union, mem_sdiff, psi_mk]
    by_cases huC : u ∈ C <;> by_cases huM : u ∈ M <;> by_cases huX : u ∈ X <;>
      by_cases hvC : v ∈ C <;> by_cases hvM : v ∈ M <;> by_cases hvX : v ∈ X <;>
      simp_all

end Edge

theorem edgesIn_add_edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgesIn G A + edgesIn G B = ∑ e ∈ G.edgeFinset, phiG A B e := by
  unfold edgesIn phiG
  rw [card_filter, card_filter, ← sum_add_distrib]

/-- For fixed `C` and `M ⊆ Cᶜ`, the swapping inequality summed over the `2^{|M|}` pairs. -/
theorem fiber_le (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (C M : Finset V) (hMC : M ⊆ Cᶜ) :
    ∑ X ∈ M.powerset, q ^ (edgesIn G (C ∪ X) + edgesIn G (C ∪ (M \ X))) ≤
      ∑ X ∈ M.powerset, q ^ (∑ e ∈ G.edgeFinset, psi (C ∪ X) (C ∪ (M \ X)) e) := by
  set E := G.edgeFinset
  set EM := E.filter (· ∈ M.sym2) with hEM
  set K := ∑ e ∈ E.filter (· ∉ M.sym2), psi C (C ∪ M) e with hK
  have hG : ∀ X ∈ M.powerset, edgesIn G (C ∪ X) + edgesIn G (C ∪ (M \ X)) =
      #(EM.filter fun e => cut X e = false) + K := by
    intro X hX
    have hXM := mem_powerset.mp hX
    rw [edgesIn_add_edgesIn, ← sum_filter_add_sum_filter_not E (· ∈ M.sym2)]
    congr 1
    · rw [card_filter]
      refine sum_congr rfl fun e he => ?_
      rw [phiG_inside hMC (mem_filter.mp he).2]
      cases cut X e <;> rfl
    · exact sum_congr rfl fun e he => phiG_outside hMC hXM (mem_filter.mp he).2
  have hZ : ∀ X ∈ M.powerset, ∑ e ∈ E, psi (C ∪ X) (C ∪ (M \ X)) e =
      #(EM.filter fun e => cut X e = true) + K := by
    intro X hX
    have hXM := mem_powerset.mp hX
    rw [← sum_filter_add_sum_filter_not E (· ∈ M.sym2)]
    congr 1
    · rw [card_filter]
      exact sum_congr rfl fun e he => psi_inside hMC (mem_filter.mp he).2
    · exact sum_congr rfl fun e he => psi_outside hMC hXM (mem_filter.mp he).2
  rw [sum_congr rfl fun X hX => congrArg (q ^ ·) (hG X hX),
    sum_congr rfl fun X hX => congrArg (q ^ ·) (hZ X hX)]
  simp only [pow_add, ← sum_mul]
  exact mul_le_mul_of_nonneg_right (cut_lemma M EM hq0 hq1) (pow_nonneg hq0 K)

/-- **Swapping inequality**: `P_G(q)² ≤ P_{G × K₂}(q)` for `0 ≤ q ≤ 1`. -/
theorem swap (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ A : Finset V, q ^ edgesIn G A) ^ 2 ≤
      ∑ A : Finset V, ∑ B : Finset V, q ^ (∑ e ∈ G.edgeFinset, psi A B e) := by
  calc (∑ A : Finset V, q ^ edgesIn G A) ^ 2
      = ∑ A : Finset V, ∑ B : Finset V, q ^ (edgesIn G A + edgesIn G B) := by
        rw [sq, sum_mul_sum]
        simp only [pow_add]
    _ = ∑ C : Finset V, ∑ M ∈ Cᶜ.powerset, ∑ X ∈ M.powerset,
          q ^ (edgesIn G (C ∪ X) + edgesIn G (C ∪ (M \ X))) :=
        sum_pairs_reindex fun A B => q ^ (edgesIn G A + edgesIn G B)
    _ ≤ ∑ C : Finset V, ∑ M ∈ Cᶜ.powerset, ∑ X ∈ M.powerset,
          q ^ (∑ e ∈ G.edgeFinset, psi (C ∪ X) (C ∪ (M \ X)) e) := by
        apply sum_le_sum
        intro C _
        apply sum_le_sum
        intro M hM
        exact fiber_le G hq0 hq1 C M (mem_powerset.mp hM)
    _ = ∑ A : Finset V, ∑ B : Finset V, q ^ (∑ e ∈ G.edgeFinset, psi A B e) :=
        (sum_pairs_reindex fun A B => q ^ (∑ e ∈ G.edgeFinset, psi A B e)).symm

/-- Double counting of ordered adjacent pairs: `∑_{e ∈ E} ψ_{A,B}(e) = ∑_{v ∈ B} |A ∩ N(v)|`. -/
theorem sum_psi (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    ∑ e ∈ G.edgeFinset, psi A B e = ∑ v ∈ B, #(A ∩ G.neighborFinset v) := by
  set P := (A ×ˢ B).filter fun p : V × V => G.Adj p.1 p.2 with hP
  have h1 : #P = ∑ v ∈ B, #(A ∩ G.neighborFinset v) := by
    rw [hP, card_filter, sum_product_right]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_filter]
    congr 1
    ext u
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  have h2 : #P = ∑ e ∈ G.edgeFinset, psi A B e := by
    rw [card_eq_sum_card_fiberwise (f := fun p : V × V => s(p.1, p.2)) (t := G.edgeFinset)]
    · refine sum_congr rfl fun e he => ?_
      induction e using Sym2.ind with
      | h u v =>
        have huv : G.Adj u v := by simpa using he
        have hne : u ≠ v := G.ne_of_adj huv
        have hfib : (P.filter fun p => s(p.1, p.2) = s(u, v)) =
            ({(u, v), (v, u)} : Finset (V × V)).filter (· ∈ P) := by
          ext ⟨a, b⟩
          simp only [hP, mem_filter, mem_product, mem_insert, mem_singleton, Sym2.eq_iff,
            Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hab, hadj⟩, h | h⟩
            · exact ⟨Or.inl h, hab, hadj⟩
            · exact ⟨Or.inr h, hab, hadj⟩
          · rintro ⟨h | h, hab, hadj⟩
            · exact ⟨⟨hab, hadj⟩, Or.inl h⟩
            · exact ⟨⟨hab, hadj⟩, Or.inr h⟩
        have hpair : (u, v) ≠ (v, u) := by
          intro h
          exact hne (Prod.mk.inj h).1
        rw [hfib, card_filter, sum_pair hpair, psi_mk]
        simp [hP, huv, G.adj_symm huv]
    · intro p hp
      have hp' := Finset.mem_coe.mp hp
      rw [hP, mem_filter] at hp'
      simpa using hp'.2
  rw [← h1, h2]

/-- `P_{G × K₂}(q)` in vertex form: `∑_{A,B} q^{e(A,B)} = ∑_A ∏_v (1 + q^{|A ∩ N(v)|})`. -/
theorem sum_pairs_psi (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) :
    ∑ A : Finset V, ∑ B : Finset V, q ^ (∑ e ∈ G.edgeFinset, psi A B e) =
      ∑ A : Finset V, ∏ v, (1 + q ^ #(A ∩ G.neighborFinset v)) := by
  refine sum_congr rfl fun A _ => ?_
  rw [prod_one_add, powerset_univ]
  refine sum_congr rfl fun B _ => ?_
  rw [sum_psi, prod_pow_eq_pow_sum]

end Swap

end P3SSSZ
