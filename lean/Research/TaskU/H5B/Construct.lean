import Research.TaskU.H5B.Insert
import Research.TaskU.H5B.RowsValue
import Research.TaskU.H5B.LiftShift

namespace TaskU.H5.Spectrum
open Finset
noncomputable section
theorem high_sufficient (m : ℤ) : ∃ f : H → ℤ, groupDet f = 5^33*m := by
  obtain ⟨s,hs⟩ := seed_residues (m:F)
  have hdiv : (5:ℤ) ∣ m-seedA s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    rw [hs,sub_self]
  obtain ⟨k,hk⟩ := hdiv
  let q : F → ℤ := fun _ => k
  obtain ⟨f,hm,hn⟩ := lift_shift s q
  have hz : (∑ a, (q a:F)) = 0 := by simp [q,ZMod.card,show (5:F)=0 by decide]
  rw [ite_eq_left hz] at hn
  refine ⟨f,?_⟩
  rw [rows_value s q f hm,hn]
  have hq : profile q = Cyc5.scalar 0 := by ext <;> simp [profile,q,Cyc5.scalar]
  have hv (v : Cyc5.V) : Cyc5.add v (Cyc5.mul (Cyc5.scalar 5) (Cyc5.scalar 0))=v := by
    ext <;> simp [Cyc5.add,Cyc5.mul,Cyc5.scalar]
  rw [hq,hv,(swapped_data s).2.1]
  simp only [q,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  linear_combination -(5:ℤ)^33*hk

theorem low_sufficient {n : ℤ} {ℓ : ℕ} (hl : ChallengeB.visible ℓ) (hd : (ℓ:ℤ) ∣ n) :
    ∃ f : H → ℤ, groupDet f=5^28*n := by
  obtain ⟨k,rfl⟩ := hd
  obtain ⟨s,q,ht,hz,hs⟩ := insert_rows hl k
  obtain ⟨f,hm,hn⟩ := lift_shift s q
  rw [ite_eq_right hz] at hn
  refine ⟨f,?_⟩
  rw [rows_value s q f hm,ht,hs,hn]
  ring

end
end TaskU.H5.Spectrum
