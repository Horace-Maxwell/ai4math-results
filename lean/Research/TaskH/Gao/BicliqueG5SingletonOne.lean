import Research.TaskH.Gao.CaseThreeTwinDeletion
import Research.TaskH.Gao.Challenge

/-! Primary648--652. The actual graph deletes x,y; only its connectivity
test adds the u-v edge. Child order and degree are proved, not supplied. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g5_twin_carrier_card_ge_three [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (k : ℕ) [Fintype (case3TwinCarrier x y)]
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (hpq : p ≠ q) (hk : 3 ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    3 ≤ Fintype.card (case3TwinCarrier x y) := by
  classical
  have hdegree := hd p hp.1 hp.2
  have hex : ∃ z, G.Adj p z ∧ z ≠ x ∧ z ≠ y ∧ z ≠ q := by
    by_contra hno
    have hsub : G.neighborSet p ⊆ insert x (insert y ({q} : Set V)) := by
      intro z ez
      by_cases hzx : z = x
      · exact Or.inl hzx
      · by_cases hzy : z = y
        · exact Or.inr (Or.inl hzy)
        · by_cases hzq : z = q
          · exact Or.inr (Or.inr hzq)
          · exact False.elim (hno ⟨z, ez, hzx, hzy, hzq⟩)
    have hb := Set.ncard_le_ncard hsub
    have hxcard := Set.ncard_insert_le x (insert y ({q} : Set V))
    have hycard := Set.ncard_insert_le y ({q} : Set V)
    simp only [Set.ncard_singleton] at hycard
    omega
  obtain ⟨z, epz, hzx, hzy, hzq⟩ := hex
  let pr : case3TwinCarrier x y := ⟨p, hp⟩
  let qr : case3TwinCarrier x y := ⟨q, hq⟩
  let zr : case3TwinCarrier x y := ⟨z, hzx, hzy⟩
  have hpq' : pr ≠ qr := fun he => hpq (congrArg Subtype.val he)
  have hpz : pr ≠ zr := fun he => epz.ne (congrArg Subtype.val he)
  have hqz : qr ≠ zr := fun he => hzq (congrArg Subtype.val he).symm
  exact Fintype.two_lt_card_iff.mpr ⟨pr, qr, zr, hpq', hpz, hqz⟩

theorem g5_twin_original_nonroot_degree [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (k : ℕ)
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (hNx : G.neighborSet x = ({p, q} : Set V))
    (hNy : G.neighborSet y = ({p, q} : Set V))
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (G.induce (case3TwinCarrier x y))
      (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩ (k + 1) := by
  intro z hzp hzq
  have hzp' : z.1 ≠ p := fun he => hzp (Subtype.ext he)
  have hzq' : z.1 ≠ q := fun he => hzq (Subtype.ext he)
  have hclose : ∀ a, G.Adj z.1 a → a ∈ case3TwinCarrier x y := by
    intro a eza
    constructor
    · intro hax
      have exz : G.Adj x z.1 := (hax ▸ eza).symm
      have hzpair : z.1 ∈ ({p, q} : Set V) := hNx ▸ exz
      exact hzpair.elim hzp' hzq'
    · intro hay
      have eyz : G.Adj y z.1 := (hay ▸ eza).symm
      have hzpair : z.1 ∈ ({p, q} : Set V) := hNy ▸ eyz
      exact hzpair.elim hzp' hzq'
  have he : (G.neighborSet z.1).ncard =
      ((G.induce (case3TwinCarrier x y)).neighborSet z).ncard := by
    apply Set.ncard_congr (fun a ha => (⟨a, hclose a ha⟩ : case3TwinCarrier x y))
    · intro a ha
      exact ha
    · intro a b _ha _hb hab
      exact congrArg Subtype.val hab
    · intro a ha
      exact ⟨a.1, ha, Subtype.ext rfl⟩
  rw [← he]
  exact hd z.1 z.2.1 z.2.2

theorem g5_two_neighbor_original_family [Fintype V] (G : SimpleGraph V)
    (A : Set V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hk : 3 ≤ k)
    (hA : A.ncard = 2) (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  obtain ⟨u, v, huv, hpair⟩ := Set.ncard_eq_two.mp hA
  have hNx' : G.neighborSet x = ({u, v} : Set V) := hNx.trans hpair
  have hNy' : G.neighborSet y = ({u, v} : Set V) := hNy.trans hpair
  have exu : G.Adj x u := by
    change u ∈ G.neighborSet x
    rw [hNx']
    exact Or.inl rfl
  have exv : G.Adj x v := by
    change v ∈ G.neighborSet x
    rw [hNx']
    exact Or.inr rfl
  have eyu : G.Adj y u := by
    change u ∈ G.neighborSet y
    rw [hNy']
    exact Or.inl rfl
  have eyv : G.Adj y v := by
    change v ∈ G.neighborSet y
    rw [hNy']
    exact Or.inr rfl
  let D := case3TwinCarrier x y
  let : Fintype D := Fintype.ofFinite _
  have huD : u ∈ D := ⟨exu.ne.symm, eyu.ne.symm⟩
  have hvD : v ∈ D := ⟨exv.ne.symm, eyv.ne.symm⟩
  let ur : D := ⟨u, huD⟩
  let vr : D := ⟨v, hvD⟩
  have hcard := g5_twin_carrier_card_ge_three G x y u v k huD hvD huv hk hd
  have hroot := case3_twin_deleted_graph_rooted G x y u v huD hvD huv hNx' hNy' hG hcard
  have hdegree := g5_twin_original_nonroot_degree G x y u v k huD hvD hNx' hNy' hd
  have hlt : Fintype.card D < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective (fun z : D => (z : V)) Subtype.val_injective
    intro hsurj
    obtain ⟨z, hzx⟩ := hsurj x
    exact z.2.1 hzx
  obtain ⟨a, step, ps, hps⟩ := ih D (G.induce D) ur vr k hlt (by omega) hroot hdegree
  let f : G.induce D →g G := (SimpleGraph.Embedding.induce D).toHom
  let q : Fin k → G.Walk u v := fun i => (ps i).map f
  have hq : AdmissiblePathFamily G u v k a step q :=
    (admissible_family_map (G.induce D) G f Subtype.val_injective ur vr k a step ps hps).1
  have hxq : ∀ i, x ∉ (q i).support := by
    intro i hx
    have hx' : x ∈ ((ps i).map f).support := hx
    rw [Walk.support_map] at hx'
    obtain ⟨z, _hz, he⟩ := List.mem_map.mp hx'
    exact z.2.1 he
  let F : Fin k → G.Walk x v := fun i => Walk.cons exu (q i)
  have hFP : ∀ i, (F i).IsPath := fun i => (hq.2.2 i).1.cons (hxq i)
  have hyF : ∀ i, y ∉ (F i).support := by
    intro i hy
    change y ∈ x :: (q i).support at hy
    rcases List.mem_cons.mp hy with he | hy
    · exact hxy he.symm
    · have hy' : y ∈ ((ps i).map f).support := hy
      rw [Walk.support_map] at hy'
      obtain ⟨z, _hz, he⟩ := List.mem_map.mp hy'
      exact z.2.2 he
  let out : Fin k → G.Walk x y := fun i => (F i).append eyv.symm.toWalk
  refine ⟨a + 2, step, out, by have hh := hq.1; omega, hq.2.1, ?_⟩
  intro i
  have hmeet : ∀ z, z ∈ (F i).support → z ∈ eyv.symm.toWalk.support → z = v := by
    intro z hzF hzE
    rw [SimpleGraph.Adj.support_toWalk] at hzE
    have he : z = v ∨ z = y := by simpa using hzE
    rcases he with he | he
    · exact he
    · exact False.elim (hyF i (Eq.mp (congrArg (fun z => z ∈ (F i).support) he) hzF))
  refine ⟨append_isPath_of_only_common_endpoint (hFP i) eyv.symm.isPath_toWalk hmeet, ?_⟩
  change ((Walk.cons exu (q i)).append eyv.symm.toWalk).length = a + 2 + i.val * step
  rw [Walk.length_append, Walk.length_cons, eyv.symm.length_toWalk, (hq.2.2 i).2]
  omega

#print axioms g5_twin_carrier_card_ge_three
#print axioms g5_twin_original_nonroot_degree
#print axioms g5_two_neighbor_original_family
end TaskH.Gao
