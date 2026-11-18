import Research.TaskH.General.OriginalBoundaryFiberSaturation
import Research.TaskH.General.WholeClassCardOriginal
import Research.TaskH.General.CliqueExteriorHookOriginal

/-! At the actual boundary degree, TWO internally derived singleton colors
bound the entire order. Real k-clique/exterior incidence then contradicts it.
The lower degree bound is the original-domain baseline, not a new premise. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
open scoped BigOperators
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_boundary_no_k_clique [DecidableRel G.Adj]
    (hk : 6 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V) (hv : G.degree v = 2 * k - 2)
    (Q : Finset V) (hQ : G.IsClique (Q : Set V)) (hcard : Q.card = k) : False := by
  classical
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedVertex hcrit v
  obtain ⟨a, b, hab, hcenters, _, _⟩ :=
    equality_original_boundary_singletons_and_pairs (by omega) hcrit hcount hnot v hv c
  have ha : a ∈ originalSingletonCenters c := by rw [hcenters]; exact Finset.mem_insert_self _ _
  have hb : b ∈ originalSingletonCenters c := by
    rw [hcenters]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hva, hau⟩ := (mem_originalSingletonCenters c).mp ha
  obtain ⟨hvb, hbu⟩ := (mem_originalSingletonCenters c).mp hb
  have hc := original_singleton_centers_color_ne c ha hb hab hva.ne.symm hvb.ne.symm
  have horder := equality_two_singletons_original_order_le (by omega) hcrit hcount
    hva hvb c hau hbu hc
  have hn : 2 * k - 1 ≤ Fintype.card V := by
    have hh := G.degree_lt_card_verts v
    omega
  have houtside : 2 ≤ Qᶜ.card := by
    have hh := Finset.card_add_card_compl Q
    rw [hcard] at hh
    omega
  have hcol : ∀ z ∈ Qᶜ, (Q.filter (fun x => G.Adj z x)).card ≤ 1 := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := Finset.exists_mem_ne (by omega : 1 < Qᶜ.card) z
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    exact equality_original_k_clique_two_exterior_hooks (by omega) hcrit hcount
      Q hQ hcard (Finset.mem_compl.mp hz) (Finset.mem_compl.mp hw) hwz.symm
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq
      (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hrow : ∀ x ∈ Q, k - 1 ≤ (Qᶜ.filter (fun z => G.Adj x z)).card := by
    intro x hx
    have hdeg := equality_original_minimum_degree_two_mul_sub_two
      (by omega) hcrit hcount hnot x
    have hinside : (Q.filter (fun z => G.Adj x z)).card ≤ k - 1 := by
      have hsub : Q.filter (fun z => G.Adj x z) ⊆ Q.erase x := by
        intro z hz
        have hh := Finset.mem_filter.mp hz
        exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hx, hcard] at hh
      exact hh
    have hpart : (Q.filter (fun z => G.Adj x z)).card +
        (Qᶜ.filter (fun z => G.Adj x z)).card = G.degree x := by
      have he : (Q.filter (fun z => G.Adj x z)) ∪
          (Qᶜ.filter (fun z => G.Adj x z)) = G.neighborFinset x := by
        ext z
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
          G.mem_neighborFinset]
        tauto
      have hd : Disjoint (Q.filter (fun z => G.Adj x z))
          (Qᶜ.filter (fun z => G.Adj x z)) := by
        apply Finset.disjoint_left.mpr
        intro z hz hz'
        exact Finset.mem_compl.mp (Finset.mem_filter.mp hz').1 (Finset.mem_filter.mp hz).1
      rw [← Finset.card_union_of_disjoint hd, he, G.card_neighborFinset_eq_degree]
    omega
  have hlo : k * (k - 1) ≤ ∑ x ∈ Q, (Qᶜ.filter (fun z => G.Adj x z)).card := by
    calc
      k * (k - 1) = ∑ _x ∈ Q, (k - 1) := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ z ∈ Qᶜ, (Q.filter (fun x => G.Adj z x)).card) ≤ Qᶜ.card := by
    calc
      _ ≤ ∑ _z ∈ Qᶜ, 1 := Finset.sum_le_sum hcol
      _ = _ := by simp
  have hdc : (∑ x ∈ Q, (Qᶜ.filter (fun z => G.Adj x z)).card) =
      ∑ z ∈ Qᶜ, (Q.filter (fun x => G.Adj x z)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsym : (∑ z ∈ Qᶜ, (Q.filter (fun x => G.Adj x z)).card) =
      ∑ z ∈ Qᶜ, (Q.filter (fun x => G.Adj z x)).card := by
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    ext x
    simp only [Finset.mem_filter, G.adj_comm]
  have hdc_symm : (∑ x ∈ Q, (Qᶜ.filter (fun z => G.Adj x z)).card) =
      ∑ z ∈ Qᶜ, (Q.filter (fun x => G.Adj z x)).card := hdc.trans hsym
  have hcQ := Finset.card_add_card_compl Q
  rw [hcard] at hcQ
  have hs : k - 1 + 1 = k := by omega
  have hmul := congrArg (fun n : ℕ => k * n) hs
  have hpow : k ^ 2 = k * k := pow_two k
  have hpow3 : 3 ≤ k ^ 2 := by nlinarith [hk]
  have horder3 : Fintype.card V + 3 ≤ k ^ 2 := by omega
  nlinarith [hlo, hhi, hdc_symm, hcQ, hmul, hpow, horder3]

end TaskH.General
#print axioms TaskH.General.equality_original_boundary_no_k_clique
