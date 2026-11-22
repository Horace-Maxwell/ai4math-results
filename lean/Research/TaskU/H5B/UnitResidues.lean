import Research.TaskU.H5B.UnitTable
import Research.TaskU.H5B.LiftRing

namespace TaskU.H5.Spectrum
open Cyc5 (V)

theorem red_difference {x y : V} (h : ChallengeB.congrFive x y) :
    ∃ w : V, x = y + (5 : V)*w := by
  rcases h with ⟨a,b,c,d⟩
  rw [Int.modEq_iff_dvd] at a b c d
  obtain ⟨a,ha⟩ := a
  obtain ⟨b,hb⟩ := b
  obtain ⟨c,hc⟩ := c
  obtain ⟨d,hd⟩ := d
  refine ⟨⟨-a,-b,-c,-d⟩,?_⟩
  change x = Cyc5.add y (Cyc5.mul (Cyc5.scalar 5) _)
  ext <;> simp [Cyc5.add,Cyc5.mul,Cyc5.scalar] <;> omega

private lemma rm_assoc (a b c : R5) : rm (rm a b) c = rm a (rm b c) := by
  have h := congrArg red (Cyc5.mul_assoc (liftR a) (liftR b) (liftR c))
  simpa only [red_mul,red_lift] using h

private lemma rm_right_one (a : R5) : rm a (red (Cyc5.scalar 1)) = a := by
  simpa only [red_mul,red_lift] using congrArg red (Cyc5.mul_scalar_one (liftR a))

private lemma red_nonzero {x : V} (h : ¬ (5:ℤ) ∣ Cyc5.norm x) : rs (red x) ≠ 0 := by
  intro he
  apply h
  apply (Cyc5.five_dvd_norm_iff _).mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
  simpa [rs,red,Cyc5.sumCoeff] using he

private lemma image_from_zero {x : V} (hz : rs (red x) ≠ 0) (he : defect (red x)=0) :
    ChallengeB.unitImage x := by
  let v := correction (red x)
  have hv : Cyc5.norm v=1 := unitRep_norm _ _
  obtain ⟨w,hw,_⟩ := unit_inverse hv
  have h := normal_table (red x) hz
  rw [he, show shape 0 = Cyc5.scalar 1 by decide] at h
  change rm (red x) (red v)=red (Cyc5.scalar 1) at h
  refine ⟨w,v,by rw [Cyc5.mul_comm]; exact hw,red_congr.mpr ?_⟩
  have hp := congrArg (fun z => rm z (red w)) h
  simp only [rm_assoc, ← red_mul v w, hw, rm_right_one] at hp
  simpa only [← red_mul, Cyc5.mul_comm (Cyc5.scalar 1), Cyc5.mul_scalar_one] using hp

theorem conjugation_fixed {x : V} (h : ¬ (5:ℤ) ∣ Cyc5.norm x)
    (hu : ∃ u, Cyc5.norm u=1 ∧ ChallengeB.congrFive (Cyc5.conj x) (Cyc5.mul u x)) :
    ChallengeB.unitImage x := by
  obtain ⟨u,hn,he⟩ := hu
  have hz := red_nonzero h
  apply image_from_zero hz
  have eqr : rm (rc (red x)) (rrInv (red x)) = red u := by
    rw [← red_conj,red_congr.mp he, red_mul,rm_assoc,inv_table _ hz,rm_right_one]
  obtain ⟨k,hk⟩ := Cyc5.unit_phase u hn
  apply fixed_table (red x) hz k
  rw [eqr, ← red_conj, hk, red_mul]

theorem visible_normalized {q : ℕ} (hv : ChallengeB.visible q) :
    ∃ η : V, ∃ d : Q5, ∃ w : V, d ≠ 0 ∧ Cyc5.norm η=(q:ℤ) ∧
      η=shape d+(5:V)*w := by
  obtain ⟨hq,hmod,x,hx,hi⟩ := hv
  have h : ¬(5:ℤ) ∣ Cyc5.norm x := by
    rw [hx]
    change ¬ ((5:ℕ):ℤ) ∣ (q:ℤ)
    rw [Int.natCast_dvd_natCast]
    omega
  have hz := red_nonzero h
  let d := defect (red x)
  have hd : d≠0 := fun he => hi (image_from_zero hz he)
  let η := Cyc5.mul x (correction (red x))
  have hn : Cyc5.norm η=(q:ℤ) := by
    rw [show η = Cyc5.mul x (correction (red x)) by rfl,Cyc5.norm_mul,show Cyc5.norm (correction (red x))=1 from unitRep_norm _ _,hx,mul_one]
  have hc : ChallengeB.congrFive η (shape d) := by
    apply red_congr.mpr
    rw [show η = Cyc5.mul x (correction (red x)) by rfl,red_mul]
    exact normal_table _ hz
  obtain ⟨w,hw⟩ := red_difference hc
  exact ⟨η,d,w,hd,hn,hw⟩

end TaskU.H5.Spectrum
