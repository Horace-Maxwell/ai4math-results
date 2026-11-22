import Research.TaskR.CSS.Geometry
import Research.TaskR.CSS.Residues

namespace TaskR.CSS.Proof

open TaskR.CSS.Challenge TaskR.CSS.Geometry

private def ztotal (x : Lattice) : ℤ := x 0 + x 1 + x 2 + x 3

private theorem upper_coordinates (a : Space) :
    ∃ (b : Space) (z : Lattice), (∀ i, 0 ≤ b i) ∧ total b ≤ 2 ∧
      mix 2 a = embed z + mix 2 b := by
  let f : Lattice := fun i => ⌊6 * a i⌋
  obtain ⟨k,hk⟩ := Residues.upper (f 0) (f 1) (f 2) (f 3)
  let n : Lattice := fun i => f i + k * weight i
  let t : Lattice := fun i => n i / 6
  let b : Space := fun i => a i + (k : ℝ) * embed weight i / 6 - (t i : ℝ)
  let z : Lattice := fun i => t i + (ztotal t - k) * weight i
  have hrep (i : Fin 4) :
      6 * b i = 6 * a i - (f i : ℝ) + ((n i % 6 : ℤ) : ℝ) := by
    have h := Int.emod_add_mul_ediv (n i) 6
    change n i % 6 + 6 * t i = f i + k * weight i at h
    have h' : ((n i % 6 : ℤ) : ℝ) + 6 * (t i : ℝ) = (f i : ℝ) + (k : ℝ) * (weight i : ℝ) := by
      exact_mod_cast h
    dsimp [b, embed]
    linarith only [h']
  have lo (i : Fin 4) : 0 ≤ b i := by
    have h₁ : (f i : ℝ) ≤ 6 * a i := Int.floor_le _
    have h₂ : (0 : ℝ) ≤ ((n i % 6 : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg (n i) (by decide : (6:ℤ) ≠ 0)
    linarith [hrep i]
  have hi (i : Fin 4) : 6 * b i < ((n i % 6 : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (6 * a i)
    change 6 * a i < (f i : ℝ) + 1 at h
    linarith only [hrep i,h]
  have hscore : (n 0 % 6 + n 1 % 6 + n 2 % 6 + n 3 % 6 : ℤ) ≤ 8 := by
    simpa [n, Residues.score, weight, mul_comm] using hk
  have hsum : (((n 0 % 6 : ℤ) : ℝ) + (n 1 % 6 : ℤ) + (n 2 % 6 : ℤ) + (n 3 % 6 : ℤ)) ≤ 8 := by exact_mod_cast hscore
  refine ⟨b,z,lo,?_,?_⟩
  · unfold total
    linarith only [hsum,hi 0,hi 1,hi 2,hi 3]
  · funext i
    fin_cases i <;> norm_num [mix,b,z,ztotal,total,embed,weight] <;> ring

private theorem coversTwo : Covers P 2 := by
  intro x
  obtain ⟨b,z,hb,hs,h⟩ := upper_coordinates (coeff 2 x)
  rw [mix_coeff] at h
  let c : Space := fun i => b i / 2
  have hc : total c ≤ 1 := by change b 0/2 + b 1/2 + b 2/2 + b 3/2 ≤ 1; unfold total at hs; linarith
  refine ⟨z,mix 1 c,mem_mix _ (fun i => div_nonneg (hb i) (by norm_num)) hc,?_⟩
  rw [h]
  congr 1
  funext i
  simp [mix,total,c]
  ring

private def base : Lattice := ![1,1,2,4]

private theorem lower_coordinates (r : ℝ) (hr : 0 ≤ r) (hlt : r < 2) :
    ¬ Covers P r := by
  intro cover
  let a : Space := fun i => ((base i : ℝ) + r/2)/6
  obtain ⟨z,y,hy,he⟩ := cover (mix r a)
  obtain ⟨hslack,hcoef⟩ := constraints hy
  let k := ztotal z
  let n : Lattice := fun i => base i + k * weight i - 6 * z i
  have point (i : Fin 4) :
      6 * (r * coeff 1 y i) = (n i : ℝ) + r/2 := by
    have h := congrArg (fun x => coeff r x i) he
    rw [coeff_mix] at h
    dsimp [coeff,slack,total,a,k,ztotal,embed] at h
    dsimp [n,k,ztotal,coeff,slack,total,embed]
    push_cast
    fin_cases i <;> norm_num [weight] at h ⊢ <;> linarith only [h]
  have npos (i : Fin 4) : 0 ≤ n i := by
    have h := mul_nonneg hr (hcoef i)
    have h' : (-1 : ℝ) < (n i : ℝ) := by linarith only [h, point i, hlt]
    have hn : (-1 : ℤ) < n i := by exact_mod_cast h'
    omega
  have hres (i : Fin 4) : ((base i + k * weight i)%6) ≤ n i := by
    have h := npos i
    dsimp only [n] at *
    omega
  have hsum : (8 : ℤ) ≤ ztotal n := by
    have h := Residues.lower k
    have h₀ := hres 0
    have h₁ := hres 1
    have h₂ := hres 2
    have h₃ := hres 3
    norm_num [base,weight,Residues.score, mul_comm] at h h₀ h₁ h₂ h₃
    unfold ztotal
    omega
  have hsum' : (8 : ℝ) ≤ (n 0 : ℝ) + n 1 + n 2 + n 3 := by exact_mod_cast hsum
  have ht : total (coeff 1 y) ≤ 1 := by rw [total_coeff]; linarith
  have bound := mul_le_mul_of_nonneg_left ht hr
  unfold total at bound
  linarith only [point 0,point 1,point 2,point 3,hsum',bound,hlt]

theorem radius : Radius := by
  refine ⟨⟨by norm_num, coversTwo⟩, ?_⟩
  rintro r ⟨hr,hc⟩
  exact le_of_not_gt (fun h => lower_coordinates r hr h hc)

end TaskR.CSS.Proof
