import Research.Backfill.Paper7.EightRemainingMoments
import Research.Backfill.Paper7.EightCountMomentProfiles

/-! Source-only coverage from the actual two moments. The four lists below are
conclusions of Presburger arithmetic, never additional graph hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def pBag (p : Fin 8 → ℕ) : Multiset ℕ :=
  ↑[p 0,p 1,p 2,p 3,p 4,p 5,p 6,p 7]
#print axioms Paper7EightCycle.pBag

theorem pBag_mem (p : Fin 8 → ℕ) (n : ℕ) : n ∈ pBag p ↔ ∃ i, p i = n := by
  constructor
  · simp only [pBag,Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false] at *
    rintro (h|h|h|h|h|h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩
    · exact ⟨4,h.symm⟩
    · exact ⟨5,h.symm⟩
    · exact ⟨6,h.symm⟩
    · exact ⟨7,h.symm⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [pBag]
#print axioms Paper7EightCycle.pBag_mem

theorem fourteen_count_cover (c : Fin 14 → ℕ)
    (hc : ∑ j, c j = 8)
    (hs : ∑ j, j.val*c j = 26)
    (hq : ∑ j, j.val^2*c j = 242) :
    c = ![3,1,2,0,0,0,0,0,1,0,0,0,0,1] ∨
    c = ![4,1,0,0,0,0,2,0,0,0,0,0,0,1] ∨
    c = ![4,1,0,0,1,0,0,0,0,1,0,0,1,0] ∨
    c = ![5,0,0,0,0,0,0,2,0,0,0,0,1,0] := by
  rcases Paper7EightCount.moment_positive_cover c hs hq with ha|hb|he|hd
  · have hp : ∀ j : Fin 14, 0 < j.val →
        c j = (![0,1,2,0,0,0,0,0,1,0,0,0,0,1] : Fin 14 → ℕ) j := ha
    have hcard := hc
    norm_num [Fin.sum_univ_succ,hp] at hcard
    have h0 : c 0 = 3 := by omega
    left
    funext j
    fin_cases j
    · exact h0
    all_goals exact hp _ (by decide)
  · have hp : ∀ j : Fin 14, 0 < j.val →
        c j = (![0,1,0,0,0,0,2,0,0,0,0,0,0,1] : Fin 14 → ℕ) j := hb
    have hcard := hc
    norm_num [Fin.sum_univ_succ,hp] at hcard
    have h0 : c 0 = 4 := by omega
    right; left
    funext j
    fin_cases j
    · exact h0
    all_goals exact hp _ (by decide)
  · have hp : ∀ j : Fin 14, 0 < j.val →
        c j = (![0,1,0,0,1,0,0,0,0,1,0,0,1,0] : Fin 14 → ℕ) j := he
    have hcard := hc
    norm_num [Fin.sum_univ_succ,hp] at hcard
    have h0 : c 0 = 4 := by omega
    right; right; left
    funext j
    fin_cases j
    · exact h0
    all_goals exact hp _ (by decide)
  · have hp : ∀ j : Fin 14, 0 < j.val →
        c j = (![0,0,0,0,0,0,0,2,0,0,0,0,1,0] : Fin 14 → ℕ) j := hd
    have hcard := hc
    norm_num [Fin.sum_univ_succ,hp] at hcard
    have h0 : c 0 = 5 := by omega
    right; right; right
    funext j
    fin_cases j
    · exact h0
    all_goals exact hp _ (by decide)
#print axioms Paper7EightCycle.fourteen_count_cover

theorem pBag_four_cover (p : Fin 8 → ℕ) (hP : ∑ i, p i = 26)
    (hS : ∑ i, p i^2 = 242) (hcap : ∀ i, p i ≤ 13) :
    pBag p = ↑([13,8,2,2,1,0,0,0] : List ℕ) ∨
    pBag p = ↑([13,6,6,1,0,0,0,0] : List ℕ) ∨
    pBag p = ↑([12,9,4,1,0,0,0,0] : List ℕ) ∨
    pBag p = ↑([12,7,7,0,0,0,0,0] : List ℕ) := by
  let c : Fin 14 → ℕ := fun j => (pBag p).count j.val
  have hcover : ∀ n ∈ pBag p, ∃ j : Fin 14, j.val = n := by
    intro n hn
    obtain ⟨i,rfl⟩ := (pBag_mem p n).mp hn
    exact ⟨⟨p i,by have := hcap i; omega⟩,rfl⟩
  have he : Function.Injective (fun j : Fin 14 => j.val) := Fin.val_injective
  have hc : ∑ j, c j = 8 := by
    have h := Paper7PruningSpectrum.finite_count_card (pBag p) _ he hcover
    simpa [pBag,c] using h.symm
  have hs : ∑ j, j.val*c j = 26 := by
    have h := Paper7PruningSpectrum.finite_count_sum (pBag p) _ he hcover id
    have hh : (pBag p).sum = ∑ i, p i := by
      simp [pBag,Fin.sum_univ_succ]
    simpa [c,hh,hP,nsmul_eq_mul,mul_comm] using h.symm
  have hq : ∑ j, j.val^2*c j = 242 := by
    have h := Paper7PruningSpectrum.finite_count_sum (pBag p) _ he hcover
      (fun n : ℕ => n^2)
    have hh : ((pBag p).map (fun n => n^2)).sum = ∑ i, p i^2 := by
      simp [pBag,Fin.sum_univ_succ]
    simpa [c,hh,hS,nsmul_eq_mul,mul_comm] using h.symm
  have hEq (l : List ℕ) (hl : ∀ n ∈ l, n ≤ 13)
      (hcEq : ∀ j : Fin 14, c j = (↑l : Multiset ℕ).count j.val) :
      pBag p = ↑l := by
    apply Multiset.ext.mpr
    intro n
    by_cases hn : n < 14
    · exact hcEq ⟨n,hn⟩
    · have hnP : n ∉ pBag p := by
        intro hm
        obtain ⟨i,rfl⟩ := (pBag_mem p n).mp hm
        have := hcap i
        omega
      have hnL : n ∉ (↑l : Multiset ℕ) := by
        intro hm
        have := hl n (by simpa using hm)
        omega
      simp [Multiset.count_eq_zero_of_notMem hnP,
        Multiset.count_eq_zero_of_notMem hnL]
  rcases fourteen_count_cover c hc hs hq with ha|hb|hc|hd
  · left
    apply hEq _ (by simp)
    intro j
    rw [ha]
    fin_cases j <;> norm_num
  · right; left
    apply hEq _ (by simp)
    intro j
    rw [hb]
    fin_cases j <;> norm_num
  · right; right; left
    apply hEq _ (by simp)
    intro j
    rw [hc]
    fin_cases j <;> norm_num
  · right; right; right
    apply hEq _ (by simp)
    intro j
    rw [hd]
    fin_cases j <;> norm_num
#print axioms Paper7EightCycle.pBag_four_cover

theorem eight_integral_parameter_cover (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) :
    pBag p = ↑([13,8,2,2,1,0,0,0] : List ℕ) ∨
    pBag p = ↑([13,6,6,1,0,0,0,0] : List ℕ) ∨
    pBag p = ↑([12,9,4,1,0,0,0,0] : List ℕ) ∨
    pBag p = ↑([12,7,7,0,0,0,0,0] : List ℕ) := by
  exact pBag_four_cover p (eight_pure_p_remaining_profile p hp hn hG).2.1
    (eight_pure_p_squares_two_four_two p hp hn hG)
    (eight_pure_p_load_thirteen p hp hn hG)
#print axioms Paper7EightCycle.eight_integral_parameter_cover

end Paper7EightCycle
