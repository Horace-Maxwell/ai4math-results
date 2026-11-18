import Research.TaskH.Gao.CliquePrefixFamily
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.CliqueCoreDegree

/-! Local D1 transport from an actual smaller quotient family, not an E1 oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem clique_quotient_family_transport (G : SimpleGraph V) (B K : Set V)
    (x y : V) (b : B) (k : ℕ) (hBK : Disjoint B K) (hK : G.IsClique K)
    (hx : x ∈ K) (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (R : G.Walk b.1 y) (hR : R.IsPath)
    (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1)
    (hRK : ∀ z ∈ R.support, z ∉ K)
    (hchild : HasAdmissiblePaths
      (regionIdentificationGraph G B (cliqueBlockBoundary G B K x b.1)) none
      (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b.1)
        (cliqueBlock_boundary_disjoint G B K x b.1 hBK) b)) (k - K.ncard + 2)) :
    HasAdmissiblePaths G x y k := by
  classical
  let S : Set V := cliqueBlockBoundary G B K x b.1
  let m : ℕ := k - K.ncard + 2
  have hBS : Disjoint B S := cliqueBlock_boundary_disjoint G B K x b.1 hBK
  obtain ⟨a, d, p, hp⟩ := hchild
  obtain ⟨s, q, hs, hfam, _hlen, hsupp⟩ :=
    identification_induced_family_lift G (B ∪ S) S
      (regionRetainedVertex B S hBS b) m a d p hp
  dsimp only [regionRetainedVertex] at q hfam
  have hsK : ∀ i : Fin m, s i ∈ K := fun i => (hs i).1
  have hsx : ∀ i : Fin m, s i ≠ x := fun i => (hs i).2.1
  have hqK : ∀ i z, z ∈ (q i).support → z ∈ K → z = s i := by
    intro i z hz hzK
    have hh := hsupp i z hz
    rcases hh.1 with hzB | hzS
    · exact False.elim (Set.disjoint_left.mp hBK hzB hzK)
    · rcases hh.2 with he | hn
      · exact he
      · exact False.elim (hn hzS)
  have hmeetR : ∀ i z, z ∈ (q i).support → z ∈ R.support → z = b.1 := by
    intro i z hz hzR
    rcases (hsupp i z hz).1 with hzB | hzS
    · exact hRB z hzR hzB
    · exact False.elim (hRK z hzR hzS.1)
  let L : ∀ i : Fin m, G.Walk y (s i) := fun i => ((q i).append R).reverse
  have hL : ∀ i : Fin m, (L i).IsPath := by
    intro i
    exact (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hR (hmeetR i)).reverse
  have hLl : ∀ i : Fin m, (L i).length = (a + R.length) + i.val * d := by
    intro i
    change ((q i).append R).reverse.length = (a + R.length) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, (hfam.2.2 i).2]
    omega
  have hcEx : ∀ i : Fin m, ∃ c : Fin (K.ncard - 1) → G.Walk (s i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = j.val + 1 ∧ ∀ z ∈ (c j).support, z ∈ K := by
    intro i
    exact clique_prefix_family K hK ht (s i) x (hsK i) hx (hsx i)
  choose c hc using hcEx
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = s i := by
    intro i j z hzL hzc
    have hzK : z ∈ K := (hc i j).2.2 z hzc
    have hzA : z ∈ ((q i).append R).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzq | hzR
    · exact hqK i z hzq hzK
    · exact False.elim (hRK z (List.mem_of_mem_tail hzR) hzK)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hpref : 1 ≤ K.ncard - 1 := by omega
  have hbase : 2 ≤ a + R.length := by have ha := hfam.1; omega
  have hcl : ∀ i j, (c i j).length = 1 + j.val * 1 := by
    intro i j
    have hh := (hc i j).2.1
    omega
  have hyx := admissible_path_concatenation (G := G)
    hm hpref hbase (by omega : 1 ≤ (1 : ℕ)) hfam.2.1 (Or.inl rfl)
    s L c hL (fun i j => (hc i j).1) hLl hcl hmeet
  have hcount : m + (K.ncard - 1) - 1 = k := by dsimp [m]; omega
  rw [hcount] at hyx
  obtain ⟨A, D, P, hP⟩ := hyx
  exact ⟨A, D, (fun i => (P i).reverse), (admissible_family_reverse G y x k A D P hP).1⟩

#print axioms clique_quotient_family_transport
end TaskH.Gao
