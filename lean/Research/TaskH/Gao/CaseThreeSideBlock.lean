import Research.TaskH.Gao.CaseThreeKBlock
import Research.TaskH.Gao.RealRootComponentAndLift
import Research.TaskH.Gao.Base

/-! Actual p-attachment with no K attachment: lose at most one original neighbor. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_core_swap_set (K : Set V) (x p q : V) :
    insert x (insert q (insert p K)) = insert x (insert p (insert q K)) := by
  exact congrArg (fun S : Set V => insert x S) (Set.insert_comm q p K)

theorem case3_side_child_degree [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K B : Set V) (b : B) (k : ℕ)
    (hBC : Disjoint B (insert x (insert p (insert q K))))
    (hBy : y ∈ B → y = b.1) (hix : G.IsIndepSet (G.neighborSet x))
    (exq : G.Adj x q)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ ({x, p, q} : Set V))
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (realRootGraph G B p) (realRootPoint B p) (realRootBlockPoint B p b) k := by
  classical
  let S : Set V := B ∪ {p}
  intro z hzp hzb
  have hzB : z.1 ∈ B := z.2.elim id (fun he => False.elim (hzp (Subtype.ext he)))
  have hvb : z.1 ≠ b.1 := fun he => hzb (Subtype.ext he)
  have hvx : z.1 ≠ x := fun he => Set.disjoint_left.mp hBC hzB (Or.inl he)
  have hvy : z.1 ≠ y := by
    intro he
    exact hvb (he.trans (hBy (Eq.mp (congrArg (fun v : V => v ∈ B) he) hzB)))
  have hsmall : (G.neighborSet z.1 \ S).ncard ≤ 1 := by
    by_cases exv : G.Adj x z.1
    · have hsub : G.neighborSet z.1 \ S ⊆ {x} := by
        rintro w ⟨evw, hwS⟩
        rcases hcover z.1 hzB hvb w evw with hwB | hwx | hwp | hwq
        · exact False.elim (hwS (Or.inl hwB))
        · exact hwx
        · exact False.elim (hwS (Or.inr hwp))
        · have evq : G.Adj z.1 q := Eq.mp (congrArg (fun w : V => G.Adj z.1 w) hwq) evw
          exact False.elim ((case3_common_neighbor_avoids_root G x q z.1 hix exq evq.symm) exv)
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
    · have hsub : G.neighborSet z.1 \ S ⊆ {q} := by
        rintro w ⟨evw, hwS⟩
        rcases hcover z.1 hzB hvb w evw with hwB | hwx | hwp | hwq
        · exact False.elim (hwS (Or.inl hwB))
        · have evx : G.Adj z.1 x := Eq.mp (congrArg (fun w : V => G.Adj z.1 w) hwx) evw
          exact False.elim (exv evx.symm)
        · exact False.elim (hwS (Or.inr hwp))
        · exact hwq
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
  have hcard : ((realRootGraph G B p).neighborSet z).ncard = (G.neighborSet z.1 ∩ S).ncard := by
    apply Set.ncard_congr (fun w _ => w.1)
    · intro w hw; exact ⟨hw, w.2⟩
    · intro a d _ _ he; exact Subtype.ext he
    · intro w hw; exact ⟨⟨w, hw.2⟩, hw.1, rfl⟩
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet z.1) S
  have hOrig := hd z.1 hvx hvy
  rw [hcard]
  omega

theorem case3_side_block_family [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K B : Set V) (k : ℕ) [Fintype B] (b : B)
    (hK : G.IsClique K) (hsub : K ⊆ case3CoreDomain G x y p q) (ht : 2 ≤ K.ncard)
    (hk : 3 ≤ k) (hix : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (hBC : Disjoint B (insert x (insert p (insert q K))))
    (hB : TwoConnected (G.induce B)) (hBy : y ∈ B → y = b.1)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ ({x, p, q} : Set V))
    (hspoke : ∃ w ∈ B, w ≠ b.1 ∧ G.Adj p w)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (R : G.Walk b.1 y) (hR : R.IsPath)
    (hRT : ∀ z ∈ R.support, z ∉ insert x (insert p (insert q K)))
    (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (r + 1) → HasAdmissiblePaths J a d r) :
    HasAdmissiblePaths G x y k := by
  classical
  let m := k - 1
  let : Fintype (B ∪ {p} : Set V) := Fintype.ofFinite _
  have hpB : p ∉ B := fun hpB => Set.disjoint_left.mp hBC hpB (Or.inr (Or.inl rfl))
  have hBK : Disjoint B K := Set.disjoint_left.mpr
    (fun _ hv hzK => Set.disjoint_left.mp hBC hv (Or.inr (Or.inr (Or.inr hzK))))
  obtain ⟨w, hwB, hwb, epw⟩ := hspoke
  have hroot := realRoot_rooted_from_actual_spoke G B p hpB b ⟨w, hwB⟩ hB epw
    (fun he => hwb (congrArg Subtype.val he))
  have hdegree := case3_side_child_degree G x y p q K B b k hBC hBy hix exq hcover hd
  have hparam : m + 1 = k := by dsimp [m]; omega
  have hd' : NonrootDegreeAtLeast (realRootGraph G B p) (realRootPoint B p)
      (realRootBlockPoint B p b) (m + 1) := by rw [hparam]; exact hdegree
  have hltNat : Nat.card (B ∪ {p} : Set V) < Nat.card V := by
    rw [Nat.card_coe_set_eq, Set.union_singleton, Set.ncard_insert_of_notMem hpB]
    exact case3_block_strict_order B K hBK ht
  have hlt : Fintype.card (B ∪ {p} : Set V) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hchild := ih (B ∪ {p} : Set V) (realRootGraph G B p)
    (realRootPoint B p) (realRootBlockPoint B p b) m hlt hm hroot hd'
  obtain ⟨a, d, paths, hpaths⟩ := hchild
  let f : realRootGraph G B p →g G := (Embedding.induce (B ∪ {p} : Set V)).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hmap := admissible_family_map (realRootGraph G B p) G f hf
    (realRootPoint B p) (realRootBlockPoint B p b) m a d paths hpaths
  let r : Fin m → G.Walk p b.1 := fun i => (paths i).map f
  have hregion : ∀ i z, z ∈ (r i).support → z ∈ B ∨ z = p := by
    intro i z hz
    obtain ⟨w, _hw, he⟩ := (hmap.2 i z).mp hz
    have he' : w.1 = z := he
    rcases w.2 with hwB | hwp
    · exact Or.inl (Eq.mp (congrArg (fun w : V => w ∈ B) he') hwB)
    · exact Or.inr (he'.symm.trans hwp)
  have hmeetR : ∀ i z, z ∈ (r i).support → z ∈ R.support → z = b.1 := by
    intro i z hz hzR
    rcases hregion i z hz with hzB | hzp
    · exact hRB z hzR hzB
    · exact False.elim (hRT z hzR (Or.inr (Or.inl hzp)))
  let L : Fin m → G.Walk y p := fun i => ((r i).append R).reverse
  have hL : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hmap.1.2.2 i).1 hR (hmeetR i)).reverse
  have hLl : ∀ i, (L i).length = a + R.length + i.val * d := by
    intro i
    change ((r i).append R).reverse.length = a + R.length + i.val * d
    rw [Walk.length_reverse, Walk.length_append]
    have hh : (r i).length = a + i.val * d := (hmap.1.2.2 i).2
    omega
  obtain ⟨c, hc, hcsupp⟩ := case3_core_neighbor_family G x y p q K hK hsub ht exp exq hpq
  let C : ∀ i : Fin m, Fin K.ncard → G.Walk p x := fun _ j => (c j).reverse
  have hC : ∀ i j, (C i j).IsPath := fun _ j => (hc.2.2 j).1.reverse
  have hCl : ∀ i j, (C i j).length = 3 + j.val * 1 := by
    intro i j
    change (c j).reverse.length = 3 + j.val * 1
    rw [Walk.length_reverse]
    exact (hc.2.2 j).2
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (C i j).support → z = p := by
    intro i j z hzL hzC
    have hzC' : z ∈ (c j).support := by simpa only [C, Walk.support_reverse, List.mem_reverse] using hzC
    have hzT := hcsupp j z hzC'
    have hzA : z ∈ ((r i).append R).support := by simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzr | hzR
    · rcases hregion i z hzr with hzB | hzp
      · exact False.elim (Set.disjoint_left.mp hBC hzB hzT)
      · exact hzp
    · exact False.elim (hRT z (List.mem_of_mem_tail hzR) hzT)
  have hbase : 2 ≤ a + R.length := by have ha := hpaths.1; omega
  have hyx := admissible_path_concatenation (G := G) hm (by omega : 1 ≤ K.ncard)
    hbase (by omega : 1 ≤ (3 : ℕ)) hpaths.2.1 (Or.inl rfl)
    (fun _ => p) L C hL hC hLl hCl hmeet
  obtain ⟨A, D, ps, hps⟩ := hyx
  have hxym : HasAdmissiblePaths G x y (m + K.ncard - 1) :=
    ⟨A, D, (fun i => (ps i).reverse), (admissible_family_reverse G y x _ A D ps hps).1⟩
  exact has_admissible_initial_segment (by dsimp [m]; omega : k ≤ m + K.ncard - 1) hxym

#print axioms case3_core_swap_set
#print axioms case3_side_child_degree
#print axioms case3_side_block_family
end TaskH.Gao
