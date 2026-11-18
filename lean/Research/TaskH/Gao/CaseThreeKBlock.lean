import Research.TaskH.Gao.CaseThreeCorePaths
import Research.TaskH.Gao.CaseThreeCoreLossBudget
import Research.TaskH.Gao.CliqueBoundaryRooted
import Research.TaskH.Gao.IdentificationFamilyLift

/-! Actual Case3 K-attachment: strict child IH and varying original endpoint concatenation. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_core_reorder (K : Set V) (x p q : V) :
    insert x (insert p (insert q K)) = K ∪ ({x, p, q} : Set V) := by
  ext z
  constructor
  · rintro (hx | hp | hq | hK)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr hq))
    · exact Or.inl hK
  · rintro (hK | hx | hp | hq)
    · exact Or.inr (Or.inr (Or.inr hK))
    · exact Or.inl hx
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hq))

theorem case3_block_strict_order [Finite V] (B K : Set V)
    (hBK : Disjoint B K) (ht : 2 ≤ K.ncard) : B.ncard + 1 < Nat.card V := by
  have hn := Set.ncard_le_card (B ∪ K)
  rw [Set.ncard_union_eq hBK] at hn
  omega

theorem case3_K_block_family [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K B : Set V) (k : ℕ) [Fintype B] (b : B)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (ht : 2 ≤ K.ncard) (htk : K.ncard < k)
    (hix : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (hBC : Disjoint B (insert x (insert p (insert q K))))
    (hB : TwoConnected (G.induce B)) (hBy : y ∈ B → y = b.1)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ insert x (insert p (insert q K)))
    (hS : (cliqueBlockBoundary G B K x b.1).Nonempty)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (R : G.Walk b.1 y) (hR : R.IsPath)
    (hRT : ∀ z ∈ R.support, z ∉ insert x (insert p (insert q K)))
    (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (r + 1) → HasAdmissiblePaths J a d r) :
    HasAdmissiblePaths G x y k := by
  classical
  let S := cliqueBlockBoundary G B K x b.1
  let m := k - K.ncard
  have hBK : Disjoint B K := Set.disjoint_left.mpr
    (fun _ hv hzK => Set.disjoint_left.mp hBC hv (Or.inr (Or.inr (Or.inr hzK))))
  have hBS : Disjoint B S := cliqueBlock_boundary_disjoint G B K x b.1 hBK
  let : Fintype {w : (B ∪ S : Set V) // w.1 ∉ S} := Fintype.ofFinite _
  let : Fintype (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S}) := regionIdentificationFintype B S
  have hroot := cliqueBlock_quotient_rooted G B K x hBK b hB hS
  have hBC' : Disjoint B (K ∪ ({x, p, q} : Set V)) := by
    rw [← case3_core_reorder K x p q]
    exact hBC
  have hcover' : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K ∪ ({x, p, q} : Set V) := by
    rw [← case3_core_reorder K x p q]
    exact hcover
  have hdegree : NonrootDegreeAtLeast (regionIdentificationGraph G B S) none
      (some (regionRetainedVertex B S hBS b)) (m + 1) := by
    intro z hzn hzb
    cases z with
    | none => exact False.elim (hzn rfl)
    | some a =>
      have haB : a.1.1 ∈ B := a.1.2.elim id (fun h => False.elim (a.2 h))
      let v : B := ⟨a.1.1, haB⟩
      have hvb : v.1 ≠ b.1 := by
        intro he
        exact hzb (congrArg Option.some (Subtype.ext (Subtype.ext he)))
      have hrep : a = regionRetainedVertex B S hBS v := Subtype.ext (Subtype.ext rfl)
      change k - K.ncard + 1 ≤ ((regionIdentificationGraph G B S).neighborSet (some a)).ncard
      rw [hrep]
      exact case3_block_K_quotient_degree G x y p q K B b.1 k hK ht (by omega)
        hix exp exq hpq hBC' hBy hcover' hd v hvb
  have hltNat : Nat.card (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S}) < Nat.card V := by
    rw [regionIdentification_card B S hBS]
    exact case3_block_strict_order B K hBK ht
  have hlt : Fintype.card (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S}) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hchild := ih (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S})
    (regionIdentificationGraph G B S) none (some (regionRetainedVertex B S hBS b))
    m hlt hm hroot hdegree
  obtain ⟨a, d, tagPaths, htag⟩ := hchild
  obtain ⟨starts, lifts, hs, hfam, _hlen, hsupp⟩ := identification_induced_family_lift
    G (B ∪ S) S (regionRetainedVertex B S hBS b) m a d tagPaths htag
  dsimp only [regionRetainedVertex] at lifts hfam
  have hqT : ∀ i z, z ∈ (lifts i).support → z ∈ insert x (insert p (insert q K)) → z = starts i := by
    intro i z hz hzT
    have hh := hsupp i z hz
    rcases hh.1 with hzB | hzS
    · exact False.elim (Set.disjoint_left.mp hBC hzB hzT)
    · exact hh.2.elim id (fun hn => False.elim (hn hzS))
  have hmeetR : ∀ i z, z ∈ (lifts i).support → z ∈ R.support → z = b.1 := by
    intro i z hz hzR
    rcases (hsupp i z hz).1 with hzB | hzS
    · exact hRB z hzR hzB
    · exact False.elim (hRT z hzR (Or.inr (Or.inr (Or.inr hzS.1))))
  let L : ∀ i : Fin m, G.Walk y (starts i) := fun i => ((lifts i).append R).reverse
  have hL : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hR (hmeetR i)).reverse
  have hLl : ∀ i, (L i).length = (a + R.length) + i.val * d := by
    intro i
    change ((lifts i).append R).reverse.length = (a + R.length) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, (hfam.2.2 i).2]
    omega
  have hprefix : ∀ i : Fin m, ∃ c : Fin (K.ncard + 1) → G.Walk x (starts i),
      AdmissiblePathFamily G x (starts i) (K.ncard + 1) 2 1 c ∧
      ∀ j z, z ∈ (c j).support → z ∈ insert x (insert p (insert q K)) := by
    intro i
    exact case3_core_member_family G x y p q K hK.1.1 hK.1.2 ht exp exq hpq (starts i) (hs i).1
  choose c hc hcsupp using hprefix
  let C : ∀ i : Fin m, Fin (K.ncard + 1) → G.Walk (starts i) x := fun i j => (c i j).reverse
  have hC : ∀ i j, (C i j).IsPath := fun i j => ((hc i).2.2 j).1.reverse
  have hCl : ∀ i j, (C i j).length = 2 + j.val * 1 := by
    intro i j
    change (c i j).reverse.length = 2 + j.val * 1
    rw [Walk.length_reverse]
    exact ((hc i).2.2 j).2
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (C i j).support → z = starts i := by
    intro i j z hzL hzC
    have hzC' : z ∈ (c i j).support := by simpa only [C, Walk.support_reverse, List.mem_reverse] using hzC
    have hzT := hcsupp i j z hzC'
    have hzA : z ∈ ((lifts i).append R).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzq | hzR
    · exact hqT i z hzq hzT
    · exact False.elim (hRT z (List.mem_of_mem_tail hzR) hzT)
  have hbase : 2 ≤ a + R.length := by have ha := hfam.1; omega
  have hyx := admissible_path_concatenation (G := G) hm (by omega : 1 ≤ K.ncard + 1)
    hbase (by omega : 1 ≤ (2 : ℕ)) hfam.2.1 (Or.inl rfl) starts L C hL hC hLl hCl hmeet
  have hcount : m + (K.ncard + 1) - 1 = k := by dsimp [m]; omega
  rw [hcount] at hyx
  obtain ⟨A, D, ps, hps⟩ := hyx
  exact ⟨A, D, (fun i => (ps i).reverse), (admissible_family_reverse G y x k A D ps hps).1⟩

#print axioms case3_core_reorder
#print axioms case3_block_strict_order
#print axioms case3_K_block_family
end TaskH.Gao
