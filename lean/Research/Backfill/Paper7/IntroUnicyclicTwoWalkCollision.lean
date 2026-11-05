import Research.Backfill.Paper7.FourWalkTuples
import Research.Backfill.Paper7.UnicyclicCyclePath
import Research.Backfill.Paper7.IntroEvenBipartiteSpectrum

/-! The actual unique cycle permits at most one repeated two-step target
from a fixed vertex in a triangle-free graph. No branch profile is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTwoWalkCollision
open SimpleGraph BackfillPaper7.Challenge Paper7FourWalks

private theorem unicyclic_quad_support_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (q q' : Quad G)
    (hq : (quadWalk G q).IsCycle) (hq' : (quadWalk G q').IsCycle) :
    {z | z ∈ (quadWalk G q).support} = {z | z ∈ (quadWalk G q').support} := by
  obtain ⟨s, _hs, huniq⟩ := hG.2
  have hqE : (quadWalk G q).edges.toFinset = s :=
    huniq 4 _ ⟨q.val.1, quadWalk G q, hq, rfl, rfl⟩
  have hqE' : (quadWalk G q').edges.toFinset = s :=
    huniq 4 _ ⟨q'.val.1, quadWalk G q', hq', rfl, rfl⟩
  exact Paper7UnicyclicSchwenk.cycle_support_eq_of_edgeFinset
    (quadWalk G q) (quadWalk G q') hq hq' (hqE.trans hqE'.symm)

theorem unicyclic_common_neighbor_pair
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (v j a d : V)
    (hvj : v ≠ j) (had : a ≠ d)
    (hva : G.Adj v a) (haj : G.Adj a j)
    (hvd : G.Adj v d) (hdj : G.Adj d j) :
    ∀ k, G.Adj v k → G.Adj k j → k = a ∨ k = d := by
  let q : Quad G := ⟨(v, a, j, d), hva, haj, hdj.symm, hvd.symm⟩
  have hq : (quadWalk G q).IsCycle :=
    (quadWalk_isCycle_iff G q).mpr ⟨hvj, had⟩
  intro k hvk hkj
  by_cases hka : k = a
  · exact Or.inl hka
  let q' : Quad G := ⟨(v, a, j, k), hva, haj, hkj.symm, hvk.symm⟩
  have hq' : (quadWalk G q').IsCycle :=
    (quadWalk_isCycle_iff G q').mpr ⟨hvj, (show a ≠ k from fun h => hka (Eq.symm h))⟩
  have hs := unicyclic_quad_support_eq G b hG q' q hq' hq
  have hk' : k ∈ (quadWalk G q').support := by simp [quadWalk, q']
  have hk : k ∈ (quadWalk G q).support := (Set.ext_iff.mp hs k).mp hk'
  simp only [quadWalk, q, Walk.support_cons, Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk | hk | hk | hk
  · exact (hvk.ne hk.symm).elim
  · exact Or.inl hk
  · exact (hkj.ne hk).elim
  · exact Or.inr hk
  · exact (hvk.ne hk.symm).elim
#print axioms Paper7IntroTwoWalkCollision.unicyclic_common_neighbor_pair

theorem unicyclic_double_common_target_unique
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (v j k a d u t : V) (hvj : v ≠ j) (hvk : v ≠ k)
    (had : a ≠ d) (hut : u ≠ t)
    (hva : G.Adj v a) (haj : G.Adj a j)
    (hvd : G.Adj v d) (hdj : G.Adj d j)
    (hvu : G.Adj v u) (huk : G.Adj u k)
    (hvt : G.Adj v t) (htk : G.Adj t k) : k = j := by
  let q : Quad G := ⟨(v, a, j, d), hva, haj, hdj.symm, hvd.symm⟩
  let q' : Quad G := ⟨(v, u, k, t), hvu, huk, htk.symm, hvt.symm⟩
  have hq : (quadWalk G q).IsCycle :=
    (quadWalk_isCycle_iff G q).mpr ⟨hvj, had⟩
  have hq' : (quadWalk G q').IsCycle :=
    (quadWalk_isCycle_iff G q').mpr ⟨hvk, hut⟩
  have hs := unicyclic_quad_support_eq G b hG q' q hq' hq
  have hk' : k ∈ (quadWalk G q').support := by simp [quadWalk, q']
  have hk : k ∈ (quadWalk G q).support := (Set.ext_iff.mp hs k).mp hk'
  simp only [quadWalk, q, Walk.support_cons, Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk | hk | hk | hk
  · exact (hvk hk.symm).elim
  · subst k
    exact (htriangle v u a hvu huk hva.symm).elim
  · exact hk
  · subst k
    exact (htriangle v u d hvu huk hvd.symm).elim
  · exact (hvk hk.symm).elim
#print axioms Paper7IntroTwoWalkCollision.unicyclic_double_common_target_unique

theorem unicyclic_common_card_one_exception
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (v : V) :
    ∃ q : V, ∀ j, j ≠ v →
      ((G.neighborFinset v).filter (fun a => G.Adj a j)).card ≤
        if j = q then 2 else 1 := by
  by_cases hex : ∃ j a d : V, j ≠ v ∧ a ≠ d ∧
      G.Adj v a ∧ G.Adj a j ∧ G.Adj v d ∧ G.Adj d j
  · obtain ⟨q, a, d, hqv, had, hva, haq, hvd, hdq⟩ := hex
    refine ⟨q, ?_⟩
    intro j hjv
    by_cases hjq : j = q
    · subst j
      rw [ite_eq_left rfl]
      have hs : (G.neighborFinset v).filter (fun k => G.Adj k q) ⊆ {a, d} := by
        intro k hk
        obtain ⟨hkN, hkq⟩ := Finset.mem_filter.mp hk
        have h := unicyclic_common_neighbor_pair G b hG v q a d hqv.symm had
          hva haq hvd hdq k ((G.mem_neighborFinset v k).mp hkN) hkq
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h
      have hcard := Finset.card_le_card hs
      rwa [Finset.card_pair had] at hcard
    · rw [ite_eq_right hjq]
      apply Finset.card_le_one.mpr
      intro u hu t ht
      obtain ⟨huN, huj⟩ := Finset.mem_filter.mp hu
      obtain ⟨htN, htj⟩ := Finset.mem_filter.mp ht
      by_contra hut
      exact hjq (unicyclic_double_common_target_unique G b hG htriangle
        v q j a d u t hqv.symm hjv.symm had hut hva haq hvd hdq
        ((G.mem_neighborFinset v u).mp huN) huj
        ((G.mem_neighborFinset v t).mp htN) htj)
  · refine ⟨v, ?_⟩
    intro j hjv
    rw [ite_eq_right hjv]
    apply Finset.card_le_one.mpr
    intro a ha d hd
    obtain ⟨haN, haj⟩ := Finset.mem_filter.mp ha
    obtain ⟨hdN, hdj⟩ := Finset.mem_filter.mp hd
    by_contra had
    exact hex ⟨j, a, d, hjv, had, (G.mem_neighborFinset v a).mp haN, haj,
      (G.mem_neighborFinset v d).mp hdN, hdj⟩
#print axioms Paper7IntroTwoWalkCollision.unicyclic_common_card_one_exception

theorem even_unicyclic_no_triangle
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Even b) :
    ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False := by
  have hcolor := Paper7IntroEven.even_unicyclic_colorable_two G b hG hb
  intro i j k hij hjk hki
  have h := (SimpleGraph.two_colorable_iff_forall_loop_even.mp hcolor) i
    (Walk.cons hij (Walk.cons hjk (Walk.cons hki Walk.nil)))
  norm_num only [Walk.length_cons, Walk.length_nil] at h
#print axioms Paper7IntroTwoWalkCollision.even_unicyclic_no_triangle

end Paper7IntroTwoWalkCollision
