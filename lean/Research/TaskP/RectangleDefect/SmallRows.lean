import Research.TaskP.RectangleDefect.RowSplit
namespace TaskP.RectangleDefect
open Challenge

theorem small_rowSplit {k n : ℕ} {m : Counts k} (hk : k ≤ 2) (hm : area m=2*n) :
    RowSplit m n := by
  interval_cases k
  · simp [area] at hm
    refine ⟨0,0,0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,?_⟩ <;> simp [area] <;> omega
  · have h0 : m 0=2*n := by simpa [area,Fin.sum_univ_succ] using hm
    refine ⟨fun _ => n,fun _ => n,0,?_,by simp,?_,?_⟩
    · intro i; fin_cases i; simp; omega
    · simp [area]
    · simp [area]
  · have h0 : m 0 + 2*m 1=2*n := by simpa [area,Fin.sum_univ_succ] using hm
    let a : Counts 2 := ![m 0/2,0]
    let v : Counts 2 := ![0,m 1]
    refine ⟨a,a,v,?_,?_,?_,?_⟩
    · intro i
      fin_cases i <;> simp [a,v]
      omega
    · intro i; fin_cases i <;> simp [v]
    · simp [area,a,v,Fin.sum_univ_succ];omega
    · simp [area,a,v,Fin.sum_univ_succ];omega

end TaskP.RectangleDefect
