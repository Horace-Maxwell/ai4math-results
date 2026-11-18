import Research.TaskH.Gao.CaseThreeSingletonComponent
import Research.TaskH.Gao.CaseThreeActualFragment
import Research.TaskH.Gao.CaseThreeSideBlock
import Research.TaskH.Gao.CaseThreeCoreOrder
import Research.TaskH.Gao.CliqueEmptyInductionStep

/-! Complete ordinary normalized Case3 step, with all components/attachments selected internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_original_no_triple_from_smaller_IH [Fintype V] (G : SimpleGraph V)
    (x y : V) (k : ℕ) (hG : TwoConnected G) (hxy : x ≠ y)
    (hnoedge : ¬G.Adj x y) (hk : 3 ≤ k)
    (hix : G.IsIndepSet (G.neighborSet x)) (hiy : G.IsIndepSet (G.neighborSet y))
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J s t →
      NonrootDegreeAtLeast J s t (r + 1) → HasAdmissiblePaths J s t r)
    (hcounter : ¬HasAdmissiblePaths G x y k) :
    ∀ p a q : V, p ≠ q → x ≠ a → p ≠ y → a ≠ y → q ≠ y →
      G.Adj x p → G.Adj p a → G.Adj a q → G.Adj q x →
      ∀ v : V, v ≠ x → v ≠ p → v ≠ a → v ≠ q → v ≠ y →
        ¬(G.Adj v p ∧ G.Adj v q ∧ G.Adj v a) := by
  classical
  intro p a q hpq hxa hpy hay hqy exp epa eaq eqx v hvx hvp _hva hvq hvy htriple
  have exq := eqx.symm
  have haU : a ∈ case3CoreDomain G x y p q :=
    ⟨hxa.symm, hay, epa.ne.symm, eaq.ne, epa, eaq.symm⟩
  have hvU : v ∈ case3CoreDomain G x y p q :=
    ⟨hvx, hvy, hvp, hvq, htriple.1.symm, htriple.2.1.symm⟩
  obtain ⟨K, hK, _haK, _hvK, ht⟩ := case3_actual_core_exists G x y p q a v haU hvU htriple.2.2.symm
  have htk := case3_actual_core_card_lt_k G x y p q K hK.1.1 hK.1.2 ht hG hxy hpy hqy
    exp exq hpq k hcounter
  let T := insert x (insert p (insert q K))
  have hyT : y ∉ T := by
    rintro (hyx | hyp | hyq | hyK)
    · exact hxy hyx.symm
    · exact hpy hyp.symm
    · exact hqy hyq.symm
    · exact (hK.1.2 hyK).2.1 rfl
  let C := (G.induce Tᶜ).connectedComponentMk ⟨y, hyT⟩
  let yr : C.supp := ⟨⟨y, hyT⟩, rfl⟩
  let : Fintype C.supp := Fintype.ofFinite _
  by_cases hsmall : Nat.card C.supp ≤ 1
  · exact hcounter (case3_singleton_component_family G x y p q K k hG hxy hnoedge (by omega)
      hK.1.1 hK.1.2 ht exp exq hpq hpy hqy hiy horder hd hyT hsmall ih)
  · have hC : 2 ≤ Fintype.card C.supp := by
      rw [Fintype.card_eq_nat_card]
      omega
    obtain ⟨B, b, hb, hBC, hBy, hcover, ⟨iB, hB⟩, R, hR, hRT, hRB⟩ :=
      case3_actual_component_block G x y p q K k C yr rfl hC hK ht htk hix exp exq hpq hd hcounter
    let : Fintype B := iB
    let br : B := ⟨b, hb⟩
    by_cases hS : (cliqueBlockBoundary G B K x b).Nonempty
    · exact hcounter (case3_K_block_family G x y p q K B k br hK ht htk hix exp exq hpq
        hBC hB hBy hcover hS hd R hR hRT hRB ih)
    · have hcover3 : ∀ w ∈ B, w ≠ b → ∀ z, G.Adj w z → z ∈ B ∨ z ∈ ({x, p, q} : Set V) := by
        intro w hw hwb z ewz
        rcases hcover w hw hwb z ewz with hzB | hzx | hzp | hzq | hzK
        · exact Or.inl hzB
        · exact Or.inr (Or.inl hzx)
        · exact Or.inr (Or.inr (Or.inl hzp))
        · exact Or.inr (Or.inr (Or.inr hzq))
        · exact False.elim (hS ⟨z, hzK, (hK.1.2 hzK).1, w, hw, hwb, ewz⟩)
      by_cases hP : ∃ w ∈ B, w ≠ b ∧ G.Adj p w
      · exact hcounter (case3_side_block_family G x y p q K B k br hK.1.1 hK.1.2 ht hk hix
          exp exq hpq hBC hB hBy hcover3 hP hd R hR hRT hRB ih)
      · by_cases hQ : ∃ w ∈ B, w ≠ b ∧ G.Adj q w
        · have hsubSwap : K ⊆ case3CoreDomain G x y q p := by
            rw [case3CoreDomain_swap G x y p q]
            exact hK.1.2
          have hBCswap : Disjoint B (insert x (insert q (insert p K))) := by
            rw [case3_core_swap_set K x p q]
            exact hBC
          have htripleSwap : ({x, q, p} : Set V) = {x, p, q} := by
            ext z
            constructor
            · rintro (hzx | hzq | hzp)
              · exact Or.inl hzx
              · exact Or.inr (Or.inr hzq)
              · exact Or.inr (Or.inl hzp)
            · rintro (hzx | hzp | hzq)
              · exact Or.inl hzx
              · exact Or.inr (Or.inr hzp)
              · exact Or.inr (Or.inl hzq)
          have hcoverSwap : ∀ w ∈ B, w ≠ b → ∀ z, G.Adj w z → z ∈ B ∨ z ∈ ({x, q, p} : Set V) := by
            rw [htripleSwap]
            exact hcover3
          have hRTswap : ∀ z ∈ R.support, z ∉ insert x (insert q (insert p K)) := by
            rw [case3_core_swap_set K x p q]
            exact hRT
          exact hcounter (case3_side_block_family G x y q p K B k br hK.1.1 hsubSwap ht hk hix
            exq exp hpq.symm hBCswap hB hBy hcoverSwap hQ hd R hR hRTswap hRB ih)
        · have hcoverX : ∀ w ∈ B, w ≠ b → ∀ z, G.Adj w z → z ∈ B ∨ z = x := by
            intro w hw hwb z ewz
            rcases hcover3 w hw hwb z ewz with hzB | hzx | hzp | hzq
            · exact Or.inl hzB
            · exact Or.inr hzx
            · have epw : G.Adj p w := (Eq.mp (congrArg (fun z : V => G.Adj w z) hzp) ewz).symm
              exact False.elim (hP ⟨w, hw, hwb, epw⟩)
            · have eqw : G.Adj q w := (Eq.mp (congrArg (fun z : V => G.Adj w z) hzq) ewz).symm
              exact False.elim (hQ ⟨w, hw, hwb, eqw⟩)
          let L := insert x K
          have hxK : x ∉ K := fun hxK => (hK.1.2 hxK).1 rfl
          have hLcard : 3 ≤ L.ncard := by
            change 3 ≤ (insert x K).ncard
            rw [Set.ncard_insert_of_notMem hxK]
            omega
          have hBL : Disjoint B L := by
            apply Set.disjoint_left.mpr
            rintro z hzB (hzx | hzK)
            · exact Set.disjoint_left.mp hBC hzB (Or.inl hzx)
            · exact Set.disjoint_left.mp hBC hzB (Or.inr (Or.inr (Or.inr hzK)))
          have hSempty : cliqueBlockBoundary G B L x b = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro z ⟨hzL, hzx, w, hw, hwb, ewz⟩
            rcases hcoverX w hw hwb z ewz with hzB | hzx'
            · exact Set.disjoint_left.mp hBL hzB hzL
            · exact hzx hzx'
          have hcoverL : ∀ w ∈ B, w ≠ b → ∀ z, G.Adj w z → z ∈ B ∨ z ∈ L := by
            intro w hw hwb z e
            rcases hcoverX w hw hwb z e with hzB | hzx
            · exact Or.inl hzB
            · exact Or.inr (Or.inl hzx)
          let : Fintype (B ∪ {x} : Set V) := Fintype.ofFinite _
          have hxR : x ∉ R.support := fun hz => hRT x hz (Or.inl rfl)
          exact hcounter (clique_empty_branch_from_smaller_IH G B L x y k br hG hB hBL
            (Or.inl rfl) hLcard (by omega) hBy hd hSempty hcoverL R hR hxR hRB ih)

#print axioms case3_original_no_triple_from_smaller_IH
end TaskH.Gao
