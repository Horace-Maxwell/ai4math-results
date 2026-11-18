import Research.TaskH.General.OriginalMinimumDegreeBaseline

/-! Exact saturation of the ORIGINAL root-neighbor partition at degree 2k-2.
No whole deleted color class is substituted for a root-neighbor fiber. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open scoped Classical
open SimpleGraph _root_.TaskH.Challenge
open scoped BigOperators
variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_boundary_singletons_and_pairs [DecidableRel G.Adj]
    (hk : 5 ≤ k) (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hnot : ¬IsCompleteOfOrder G (k + 1)) (v : V)
    (hv : G.degree v = 2 * k - 2)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k)) :
    ∃ a b : V, a ≠ b ∧ originalSingletonCenters c = {a, b} ∧
      (originalSingletonPalette c).card = 2 ∧
      ∀ i ∉ originalSingletonPalette c,
        (Finset.univ.filter (fun z : G.neighborSet v => _root_.TaskH.neighborColor v c z = i)).card = 2 := by
  classical
  let F : Fin k → Finset (G.neighborSet v) := fun i =>
    Finset.univ.filter (fun z => _root_.TaskH.neighborColor v c z = i)
  have hpositive : ∀ i, 1 ≤ (F i).card := by
    intro i
    obtain ⟨z, hz⟩ := _root_.TaskH.critical_neighborColor_surjective hcrit v c i
    have hm : z ∈ F i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hp : 0 < (F i).card := Finset.card_pos.mpr ⟨z, hm⟩
    omega
  have hone : ∀ i, (F i).card = 1 → i ∈ originalSingletonPalette c := by
    intro i hFi
    obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hFi
    have hnF : n ∈ F i := by rw [hn]; exact Finset.mem_singleton_self _
    have hni : _root_.TaskH.neighborColor v c n = i := (Finset.mem_filter.mp hnF).2
    have hvn : G.Adj v n.val := (G.mem_neighborSet v n.val).mp n.property
    have hnJ : n.val ∈ originalSingletonCenters c := by
      apply (mem_originalSingletonCenters c).mpr
      refine ⟨hvn, ?_⟩
      intro z hzv hvz hc
      have hzF : (⟨z, hvz⟩ : G.neighborSet v) ∈ F i := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hc.trans hni
      have he : (⟨z, hvz⟩ : G.neighborSet v) = n :=
        Finset.mem_singleton.mp (by rw [← hn]; exact hzF)
      exact congrArg Subtype.val he
    have hpal := original_singleton_color_mem_palette c hnJ hvn.ne.symm
    exact hni ▸ hpal
  have hpoint : ∀ i, 2 ≤ (F i).card + if i ∈ originalSingletonPalette c then 1 else 0 := by
    intro i
    have hp := hpositive i
    by_cases hi : i ∈ originalSingletonPalette c
    · rw [ite_eq_left hi]
      omega
    · rw [ite_eq_right hi]
      have hn : (F i).card ≠ 1 := fun he => hi (hone i he)
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => hpoint i)
  have hdegree : (∑ i : Fin k, (F i).card) = G.degree v := by
    have he := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (G.neighborSet v)))
      (t := (Finset.univ : Finset (Fin k))) (f := _root_.TaskH.neighborColor v c)
      (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ, G.card_neighborSet_eq_degree] using he.symm
  have hindicator : (∑ i : Fin k, if i ∈ originalSingletonPalette c then 1 else 0) =
      (originalSingletonPalette c).card := by
    rw [← Finset.card_filter]
    simp
  rw [Finset.sum_add_distrib, hdegree, hindicator] at hsum
  have hsum' : 2 * k ≤ G.degree v + (originalSingletonPalette c).card := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_comm] using hsum
  have hq := equality_original_singleton_centers_le_two hk hcrit hcount hnot c
  have he := original_singleton_palette_card c
  have hpal : (originalSingletonPalette c).card = 2 := by omega
  have hJ : (originalSingletonCenters c).card = 2 := by omega
  have htotal : (∑ i : Fin k, ((F i).card + if i ∈ originalSingletonPalette c then 1 else 0)) = 2 * k := by
    rw [Finset.sum_add_distrib, hdegree, hindicator, hpal, hv]
    omega
  have hpaired : ∀ i, i ∉ originalSingletonPalette c → (F i).card = 2 := by
    intro i hi
    let T := fun j : Fin k => (F j).card + if j ∈ originalSingletonPalette c then 1 else 0
    have hrest := Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin k)).erase i) (fun j _ => hpoint j)
    have hc : ((Finset.univ : Finset (Fin k)).erase i).card + 1 = k := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_erase_add_one (Finset.mem_univ i))
    have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) T (Finset.mem_univ i)
    change (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, T j) + T i = ∑ j : Fin k, T j at hs
    change (∑ j : Fin k, T j) = 2 * k at htotal
    have hiT : T i = (F i).card := by dsimp [T]; rw [ite_eq_right hi]; omega
    have hr : 2 * (((Finset.univ : Finset (Fin k)).erase i).card) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, T j := by
      simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hrest
    have hh := hpoint i
    rw [ite_eq_right hi] at hh
    omega
  obtain ⟨a, b, hab, hcenters⟩ := Finset.card_eq_two.mp hJ
  exact ⟨a, b, hab, hcenters, hpal, hpaired⟩

end TaskH.General
#print axioms TaskH.General.equality_original_boundary_singletons_and_pairs
