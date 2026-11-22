import Research.TaskP.GeomSimplex.Packing

namespace TaskP.GeomSimplex.Proof
open TaskP.GeomSimplex.Challenge

def tailPoint {d : ℕ} (x : Challenge.Lattice (d+1)) : Lattice d := fun i => x i.succ

def corner {d k : ℕ} (a b : Fin k → Lattice d) (e : Fin k → Bool) : Lattice d :=
  ∑ i, if e i then b i else a i

theorem translated_pack {d k : ℕ} (hk : 0 < k) {P : Set (Space d)} (hP : Convex ℝ P)
    (g : Lattice d) (a b : Fin k → Lattice d) (hne : ∀ i,a i ≠ b i)
    (h : ∀ e, realPoint (g + corner a b e) ∈ P) : packs P k := by
  classical
  let j : Fin k := ⟨0,hk⟩
  let v : Fin k → Lattice d := fun i => if i=j then g else 0
  apply pack_of_endpoints hP (fun i => v i+a i) (fun i => v i+b i)
  · intro i eq
    exact hne i (add_left_cancel eq)
  · intro e
    have he (i : Fin k) : (if e i then v i+b i else v i+a i) =
        v i+(if e i then b i else a i) := by split <;> rfl
    simpa only [he, Finset.sum_add_distrib, show ∑ i,v i = g by simp [v], corner] using h e

/-- From a box of lattice corners in a pyramid, choose the highest endpoints.
    Replace every rising edge by a unit of lattice height spent on a base edge. -/
theorem replace_rising {d k : ℕ} (a b : Fin k → Challenge.Lattice (d+1))
    (hne : ∀ i,a i ≠ b i) (hfloor : ∀ e,0 ≤ corner a b e 0)
    (u v : Lattice d) (huv : u ≠ v) :
    ∃ (H : ℤ) (A B : Fin k → Lattice d), (∀ i,A i ≠ B i) ∧
      ∀ e : Fin k → Bool, ∃ e' : Fin k → Bool, ∃ r : ℤ, 0 ≤ r ∧ r ≤ H ∧
        corner a b e' 0 = H ∧
        H • u + corner A B e = tailPoint (corner a b e') + ((H-r) • u + r • v) := by
  classical
  let high (i : Fin k) := if a i 0 ≤ b i 0 then b i else a i
  let flat (i : Fin k) := a i 0 = b i 0
  let A (i : Fin k) := if flat i then tailPoint (a i) else tailPoint (high i)
  let B (i : Fin k) := if flat i then tailPoint (b i) else tailPoint (high i)+(v-u)
  let H := ∑ i,max (a i 0) (b i 0)
  let low := ∑ i,min (a i 0) (b i 0)
  have hlow : 0 ≤ low := by
    have h := hfloor (fun i => decide (b i 0 ≤ a i 0))
    simp only [corner,Finset.sum_apply] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : b i 0 ≤ a i 0 <;> simp [hi,min_def]
    omega
  refine ⟨H,A,B,?_,?_⟩
  · intro i eq
    by_cases hi : flat i
    · have en : tailPoint (a i) = tailPoint (b i) := by simpa [A,B,hi] using eq
      apply hne i
      funext j
      refine Fin.cases hi (fun j => congrFun en j) j
    · have en : tailPoint (high i) = tailPoint (high i)+(v-u) := by simpa [A,B,hi] using eq
      apply huv
      exact (sub_eq_zero.mp (add_eq_left.mp en.symm)).symm
  · intro e
    let e' (i : Fin k) := if flat i then e i else decide (a i 0 ≤ b i 0)
    let n (i : Fin k) : ℤ := if ¬flat i ∧ e i then 1 else 0
    let r := ∑ i,n i
    have nd (i : Fin k) : n i ≤ max (a i 0) (b i 0) - min (a i 0) (b i 0) := by
      dsimp [n,flat]
      split <;> omega
    have nr : r ≤ H - low := by simpa [r,H,low,Finset.sum_sub_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => nd i)
    refine ⟨e',r,Finset.sum_nonneg (fun i _ => by dsimp [n];split <;> norm_num), by omega, ?_,?_⟩
    · simp only [corner,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hf : flat i
      · have h := hf
        change a i 0 = b i 0 at h
        cases hi : e i <;> simp [e',hf,hi,h]
      · by_cases h : a i 0 ≤ b i 0 <;> simp [e',hf,h,max_def]
    · have seg (i : Fin k) :
            (if e i then B i else A i) =
            tailPoint (if e' i then b i else a i) + n i • (v-u) := by
        by_cases hf : flat i
        · cases h : e i <;> simp [B,A,e',n,hf,h]
        · by_cases ht : a i 0 ≤ b i 0 <;> cases h : e i <;> simp [B,A,e',n,hf,h,high,ht]
      have proj : tailPoint (corner a b e') = ∑ i,tailPoint (if e' i then b i else a i) := by
        ext j
        simp [tailPoint,corner,Finset.sum_apply]
      have comb : corner A B e = tailPoint (corner a b e') + r • (v-u) := by
        rw [proj]
        simp only [corner,seg,Finset.sum_add_distrib,← Finset.sum_smul,r]
      rw [comb,sub_smul,smul_sub]
      abel

end TaskP.GeomSimplex.Proof
