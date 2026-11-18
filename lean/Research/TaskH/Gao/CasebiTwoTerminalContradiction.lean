import Research.TaskH.Gao.CasebiPairedTerminalFamily
import Research.TaskH.Gao.TwoTerminalRouteCertificate

/-!
The actual two-terminal linkage yields the original k-family contradiction.
This internal lemma accepts the precisely defined linkage output, but the
following original-cut wrapper constructs that output from real cut data.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_two_terminal_routes_contradiction [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr w : C.supp) (hY : componentVertex C yr = y)
    (hNoY : ∀ I b, TerminalFragment C.toSimpleGraph I b → yr ∉ I)
    (q : V) (hq : q ∈ A) (ewq : G.Adj (componentVertex C w) q)
    (hroute : TwoTerminalRoutes C.toSimpleGraph w yr) : False := by
  subst y
  classical
  obtain ⟨I, J, b, c, hI, hJ, hIJ, L, R, hL, hR, _hLI, _hRJ,
    hLR, hLB, hRB, hLJ, hRI⟩ := hroute
  have hyI := hNoY I b hI
  have hyJ := hNoY J c hJ
  have hrigid := casebi_feasible_second_side_rigidity G A B x (componentVertex C yr) s k
    hmax hBs hk hG htri hquad hd hno ih C yr rfl I b hI hyI
  have hxB : x ∈ B := hmax.1.2.2.1
  obtain ⟨a, haB, hax⟩ := Set.exists_ne_of_one_lt_ncard
    (by have hh := hmax.1.2.2.2.2.1; omega : 1 < B.ncard) x
  have hB : B = ({x, a} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le (show ({x, a} : Set V) ⊆ B from by
      rintro z (hzx | hza)
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hzx) hxB
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hza) haB)
    rw [Set.ncard_pair hax.symm]
    have hs1 := hrigid.1
    omega
  have hB' : B = ({a, x} : Set V) := by rw [hB]; exact Set.pair_comm x a
  let D := componentRegion C (fragmentBlock I b)
  let E := componentRegion C (fragmentBlock J c)
  let m := k - 1
  obtain ⟨ap, dp, P, hP, hPS⟩ := casebi_actual_terminal_child_family G A B x
    (componentVertex C yr) x a s k hmax hBs hk hG htri hquad hd hno ih C yr rfl I b hI hyI hxB hB
  obtain ⟨aq, dq, Q, hQ, hQS⟩ := casebi_actual_terminal_child_family G A B x
    (componentVertex C yr) a x s k hmax hBs hk hG htri hquad hd hno ih C yr rfl J c hJ hyJ haB hB'
  let f : C.toSimpleGraph →g G := componentVertexHom C
  let l : G.Walk (componentVertex C b) (componentVertex C w) := L.map f
  let r : G.Walk (componentVertex C c) (componentVertex C yr) := R.map f
  have hmap : ∀ {v t : C.supp} (p : C.toSimpleGraph.Walk v t) (z : V),
      z ∈ (p.map f).support ↔ ∃ u ∈ p.support, componentVertex C u = z := by
    intro v t p z
    rw [Walk.support_map]
    constructor
    · intro hz
      obtain ⟨u, hu, he⟩ := List.mem_map.mp hz
      have he' : componentVertex C u = z := he
      exact ⟨u, hu, he'⟩
    · rintro ⟨u, hu, he⟩
      apply List.mem_map.mpr
      have he' : f u = z := he
      exact ⟨u, hu, he'⟩
  have hmapQ : ∀ {v t : C.supp} (p : C.toSimpleGraph.Walk v t) z,
      z ∈ (p.map f).support → z ∉ A ∪ B := by
    intro v t p z hz
    obtain ⟨u, _hu, he⟩ := (hmap p z).mp hz
    exact Eq.mp (congrArg (fun z : V => z ∉ A ∪ B) he) u.1.2
  have hblock : ∀ {v t e : C.supp} (p : C.toSimpleGraph.Walk v t) (K : Set C.supp),
      (∀ u ∈ p.support, u ∈ K → u = e) →
      ∀ z ∈ (p.map f).support, z ∈ componentRegion C K → z = componentVertex C e := by
    intro v t e p K hp z hz hzK
    obtain ⟨u, hu, he⟩ := (hmap p z).mp hz
    obtain ⟨v, hv, hev⟩ := hzK
    have hvu : v = u := componentVertex_injective C (hev.trans he.symm)
    have hue := hp u hu (Eq.mp (congrArg (fun v : C.supp => v ∈ K) hvu) hv)
    exact he.symm.trans (congrArg (componentVertex C) hue)
  have havoid : ∀ {v t : C.supp} (p : C.toSimpleGraph.Walk v t) (K : Set C.supp),
      (∀ u ∈ p.support, u ∉ K) →
      ∀ z ∈ (p.map f).support, z ∉ componentRegion C K := by
    intro v t p K hp z hz hzK
    obtain ⟨u, hu, he⟩ := (hmap p z).mp hz
    obtain ⟨v, hv, hev⟩ := hzK
    have hvu : v = u := componentVertex_injective C (hev.trans he.symm)
    exact hp u hu (Eq.mp (congrArg (fun v : C.supp => v ∈ K) hvu) hv)
  have hDE : Disjoint D E := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, he⟩ ⟨v, hv, hev⟩
    have hvu : v = u := componentVertex_injective C (hev.trans he.symm)
    exact Set.disjoint_left.mp hIJ hu
      (Eq.mp (congrArg (fun v : C.supp => v ∈ fragmentBlock J c) hvu) hv)
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hEQ : Disjoint E (A ∪ B) := componentRegion_disjoint C (fragmentBlock J c)
  have hlnr : ∀ z ∈ l.support, z ∉ r.support := by
    intro z hzL hzR
    obtain ⟨u, hu, he⟩ := (hmap L z).mp hzL
    obtain ⟨v, hv, hev⟩ := (hmap R z).mp hzR
    have hvu : v = u := componentVertex_injective C (hev.trans he.symm)
    exact hLR u hu (Eq.mp (congrArg (fun v : C.supp => v ∈ R.support) hvu) hv)
  have hlp : l.IsPath := (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hL
  have hrp : r.IsPath := (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hR
  have hPl : ∀ i z, z ∈ (P i).support → z ∈ l.support → z = componentVertex C b := by
    intro i z hzP hzl
    rcases hPS i z hzP with hzD | hzx
    · exact hblock L (fragmentBlock I b) hLB z hzl hzD
    · exact False.elim (hmapQ L z hzl
        (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hzx) (Or.inr hxB)))
  have hQr : ∀ i z, z ∈ (Q i).support → z ∈ r.support → z = componentVertex C c := by
    intro i z hzQ hzr
    rcases hQS i z hzQ with hzE | hza
    · exact hblock R (fragmentBlock J c) hRB z hzr hzE
    · exact False.elim (hmapQ R z hzr
        (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hza) (Or.inr haB)))
  have hPL := admissible_family_append_fixed_tail G x (componentVertex C b)
    (componentVertex C w) m ap dp P l hP hlp hPl
  have hQR := admissible_family_append_fixed_tail G a (componentVertex C c)
    (componentVertex C yr) m aq dq Q r hQ hrp hQr
  let PL : Fin m → G.Walk x (componentVertex C w) := fun i => (P i).append l
  let QR : Fin m → G.Walk a (componentVertex C yr) := fun i => (Q i).append r
  have hPLQR : ∀ i j z, z ∈ (PL i).support → z ∈ (QR j).support → False := by
    intro i j z hzP hzQ
    rcases hPL.2 i z hzP with hzD | hzL
    · rcases hPS i z hzD with hzD | hzx
      · rcases hQR.2 j z hzQ with hzE | hzR
        · rcases hQS j z hzE with hzE | hza
          · exact Set.disjoint_left.mp hDE hzD hzE
          · exact Set.disjoint_left.mp hDQ hzD
              (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hza) (Or.inr haB))
        · exact havoid R (fragmentBlock I b) hRI z hzR hzD
      · rcases hQR.2 j z hzQ with hzE | hzR
        · rcases hQS j z hzE with hzE | hza
          · exact Set.disjoint_left.mp hEQ hzE
              (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hzx) (Or.inr hxB))
          · exact hax (hza.symm.trans hzx)
        · exact hmapQ R z hzR
            (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hzx) (Or.inr hxB))
    · rcases hQR.2 j z hzQ with hzE | hzR
      · rcases hQS j z hzE with hzE | hza
        · exact havoid L (fragmentBlock J c) hLJ z hzL hzE
        · exact hmapQ L z hzL
            (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) hza) (Or.inr haB))
      · exact hlnr z hzL hzR
  have hPLQ : ∀ i z, z ∈ (PL i).support → z ∈ A ∪ B → z = x := by
    intro i z hz hzQ
    rcases hPL.2 i z hz with hzP | hzL
    · rcases hPS i z hzP with hzD | he
      · exact False.elim (Set.disjoint_left.mp hDQ hzD hzQ)
      · exact he
    · exact False.elim (hmapQ L z hzL hzQ)
  have hQRQ : ∀ j z, z ∈ (QR j).support → z ∈ A ∪ B → z = a := by
    intro j z hz hzQ
    rcases hQR.2 j z hz with hzP | hzR
    · rcases hQS j z hzP with hzE | he
      · exact False.elim (Set.disjoint_left.mp hEQ hzE hzQ)
      · exact he
    · exact False.elim (hmapQ R z hzR hzQ)
  have eqa : G.Adj q a := hmax.1.2.1 q hq a haB
  let T : G.Walk (componentVertex C w) a := Walk.cons ewq eqa.toWalk
  have hwq : componentVertex C w ≠ q := ewq.ne
  have hwa : componentVertex C w ≠ a := fun he => w.1.2
    (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr haB))
  have hT : T.IsPath := eqa.isPath_toWalk.cons (by
    change componentVertex C w ∉ [q, a]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact not_or.mpr ⟨hwq, hwa⟩)
  have hTS : ∀ z ∈ T.support, z = componentVertex C w ∨ z = q ∨ z = a := by
    intro z hz
    change z ∈ [componentVertex C w, q, a] at hz
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hz
  have hxq : x ≠ q := fun he => Set.disjoint_left.mp hmax.1.1 hq
    (Eq.mp (congrArg (fun z : V => z ∈ B) he) hxB)
  have hPLT : ∀ i z, z ∈ (PL i).support → z ∈ T.support → z = componentVertex C w := by
    intro i z hzP hzT
    rcases hTS z hzT with he | he | he
    · exact he
    · have hzx := hPLQ i z hzP
        (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inl hq))
      exact False.elim (hxq (hzx.symm.trans he))
    · have hzx := hPLQ i z hzP
        (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr haB))
      exact False.elim (hax (he.symm.trans hzx))
  have hX := admissible_family_append_fixed_tail G x (componentVertex C w) a m
    (ap + l.length) dp PL T hPL.1 hT hPLT
  let X : Fin m → G.Walk x a := fun i => (PL i).append T
  have hmeet : ∀ i j z, z ∈ (X i).support → z ∈ (QR j).support → z = a := by
    intro i j z hzX hzQR
    rcases hX.2 i z hzX with hzPL | hzT
    · exact False.elim (hPLQR i j z hzPL hzQR)
    · rcases hTS z hzT with he | he | he
      · exact False.elim (hPLQR i j (componentVertex C w)
          (Walk.end_mem_support (PL i))
          (Eq.mp (congrArg (fun z : V => z ∈ (QR j).support) he) hzQR))
      · exact hQRQ j z hzQR
          (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inl hq))
      · exact he
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hall := admissible_path_concatenation (G := G) hm hm hX.1.1
    (by have hh := hQR.1.1; omega : 1 ≤ aq + r.length) hX.1.2.1 hQR.1.2.1
    (fun _ => a) X (fun _ j => QR j) (fun i => (hX.1.2.2 i).1)
    (fun _ j => (hQR.1.2.2 j).1) (fun i => (hX.1.2.2 i).2)
    (fun _ j => (hQR.1.2.2 j).2) hmeet
  exact hno (has_admissible_initial_segment (by dsimp [m]; omega : k ≤ m + m - 1) hall)

#print axioms casebi_two_terminal_routes_contradiction
end TaskH.Gao
