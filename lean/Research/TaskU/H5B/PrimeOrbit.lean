import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

namespace TaskU.H5.PrimeOrbit

theorem four_dvd {R : Type*} [CommRing R] [IsDomain R] (e : R ≃+* R)
    {a b c d : R} (ab : e a = b) (bc : e b = c) (cd : e c = d) (da : e d = a)
    (hp : Prime a) (hne : ¬a ∣ c) {q : ℕ} (hd : a ∣ (q : R)) :
    (a*c)*(b*d) ∣ (q:R) := by
  have push {x y z w : R} (hx : e x=z) (hy : e y=w) (h : x∣y) : z∣w := by
    rw [←hx,←hy]; exact map_dvd e h
  have not_ab : ¬a∣b := fun h => hne (h.trans (push ab bc h))
  have not_ad : ¬a∣d := fun h => hne (h.trans (push cd bc (push bc ab (push ab da h))))
  have not_ba : ¬b∣a := fun h => not_ad (push da cd (push cd bc (push bc ab h)))
  have not_ca : ¬c∣a := fun h => hne (push da bc (push cd ab h))
  have not_da : ¬d∣a := fun h => not_ab (push da ab h)
  have not_cb : ¬c∣b := fun h => not_ad (push da cd (push cd bc h))
  have not_db : ¬d∣b := fun h => hne (push da bc h)
  have not_dc : ¬d∣c := fun h => not_ad (push da cd h)
  have pb : Prime b := by rw [←ab]; exact (MulEquiv.prime_iff e).mpr hp
  have pc : Prime c := by rw [←bc]; exact (MulEquiv.prime_iff e).mpr pb
  have pd : Prime d := by rw [←cd]; exact (MulEquiv.prime_iff e).mpr pc
  have sb : b∣(q:R) := push ab (map_natCast e q) hd
  have sc : c∣(q:R) := push bc (map_natCast e q) sb
  have sd : d∣(q:R) := push cd (map_natCast e q) sc
  obtain ⟨t,ht⟩ := hd
  rw [ht] at sb sc sd
  obtain ⟨u,hu⟩ := (pb.dvd_mul.mp sb).resolve_left not_ba
  have hcu := (pc.dvd_mul.mp sc).resolve_left not_ca
  have hdu := (pd.dvd_mul.mp sd).resolve_left not_da
  rw [hu] at hcu hdu
  obtain ⟨v,hv⟩ := (pc.dvd_mul.mp hcu).resolve_left not_cb
  have hdv := (pd.dvd_mul.mp hdu).resolve_left not_db
  rw [hv] at hdv
  obtain ⟨w,hw⟩ := (pd.dvd_mul.mp hdv).resolve_left not_dc
  exact ⟨w,by rw [ht,hu,hv,hw]; ring⟩

theorem prime_below_nat {R : Type*} [CommRing R] [IsDomain R] {a : R} (hp : Prime a)
    {n : ℕ} (hn : n ≠ 0) (h : a ∣ (n : R)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ a ∣ (q:R) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n
      exact (hp.not_isUnit (isUnit_of_dvd_one (by simpa using h))).elim
    obtain ⟨q,hq,hqn⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨k,hk⟩ := hqn
    rw [hk, Nat.cast_mul] at h
    rcases hp.dvd_mul.mp h with hq'|hk'
    · exact ⟨q,hq,⟨k,hk⟩,hq'⟩
    · have hk0 : k≠0 := by rintro rfl; simp_all
      have hkn : k<n := by nlinarith [hq.two_le, Nat.pos_of_ne_zero hk0]
      obtain ⟨r,hr,hrk,hrs⟩ := ih k hkn hk0 hk'
      exact ⟨r,hr,by rw [hk]; exact dvd_mul_of_dvd_right hrk q,hrs⟩

end TaskU.H5.PrimeOrbit
