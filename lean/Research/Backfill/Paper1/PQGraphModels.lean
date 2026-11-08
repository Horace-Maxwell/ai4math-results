import Research.Backfill.Paper1.GraphBridge
import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset
namespace NarrowPQ

lemma val_finEquiv (n : ℕ) [NeZero n] (u : Fin n) : (ZMod.finEquiv n u).val = u.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

def crt (p q : ℕ) [NeZero p] [NeZero q] [NeZero (p * q)] (hc : p.Coprime q) :
    Fin (p * q) ≃ Fin p × Fin q :=
  (ZMod.finEquiv (p * q)).toEquiv.trans ((ZMod.chineseRemainder hc).toEquiv.trans
    (Equiv.prodCongr (ZMod.finEquiv p).symm.toEquiv (ZMod.finEquiv q).symm.toEquiv))

lemma crt_fst (p q : ℕ) [NeZero p] [NeZero q] [NeZero (p * q)]
    (hc : p.Coprime q) (u : Fin (p * q)) :
    ZMod.finEquiv p (crt p q hc u).1 = (u.val : ZMod p) := by
  change ZMod.finEquiv p ((ZMod.finEquiv p).symm
    (ZMod.chineseRemainder hc (ZMod.finEquiv (p * q) u)).1) = _
  rw [RingEquiv.apply_symm_apply]
  change (ZMod.cast (ZMod.finEquiv (p * q) u) : ZMod p × ZMod q).1 = _
  rw [Prod.fst_zmod_cast, ZMod.cast_eq_val, val_finEquiv]

lemma crt_snd (p q : ℕ) [NeZero p] [NeZero q] [NeZero (p * q)]
    (hc : p.Coprime q) (u : Fin (p * q)) :
    ZMod.finEquiv q (crt p q hc u).2 = (u.val : ZMod q) := by
  change ZMod.finEquiv q ((ZMod.finEquiv q).symm
    (ZMod.chineseRemainder hc (ZMod.finEquiv (p * q) u)).2) = _
  rw [RingEquiv.apply_symm_apply]
  change (ZMod.cast (ZMod.finEquiv (p * q) u) : ZMod p × ZMod q).2 = _
  rw [Prod.snd_zmod_cast, ZMod.cast_eq_val, val_finEquiv]

lemma coord_dvd (p q : ℕ) [NeZero p] [NeZero q] [NeZero (p * q)]
    (hc : p.Coprime q) (u v : Fin (p * q)) :
    (p ∣ (v - u).val ↔ (crt p q hc v).1 = (crt p q hc u).1) ∧
    (q ∣ (v - u).val ↔ (crt p q hc v).2 = (crt p q hc u).2) := by
  have mapmod (r : ℕ) [NeZero r] (hr : r ∣ p * q) :
      (((v - u).val : ℕ) : ZMod r) = (v.val : ZMod r) - (u.val : ZMod r) := by
    let f : ZMod (p * q) →+* ZMod r := ZMod.castHom hr (ZMod r)
    have hf (w : Fin (p * q)) : f (ZMod.finEquiv (p * q) w) = (w.val : ZMod r) := by
      change (ZMod.cast (ZMod.finEquiv (p * q) w) : ZMod r) = _
      rw [ZMod.cast_eq_val, val_finEquiv]
    have hsub : ZMod.finEquiv (p * q) (v - u) =
        ZMod.finEquiv (p * q) v - ZMod.finEquiv (p * q) u := by
      generalize hN : p * q = N at *
      cases N with
      | zero => exact False.elim (NeZero.ne 0 rfl)
      | succ n => rfl
    rw [← hf (v - u), hsub, map_sub, hf v, hf u]
  constructor
  · rw [← ZMod.natCast_eq_zero_iff, mapmod p (dvd_mul_right p q),
      sub_eq_zero, ← crt_fst p q hc v, ← crt_fst p q hc u]
    exact (ZMod.finEquiv p).injective.eq_iff
  · rw [← ZMod.natCast_eq_zero_iff, mapmod q (dvd_mul_left q p),
      sub_eq_zero, ← crt_snd p q hc v, ← crt_snd p q hc u]
    exact (ZMod.finEquiv q).injective.eq_iff

lemma gcd_classes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (v : ℕ) :
    (Nat.gcd v (p * q) = 1 ↔ ¬p ∣ v ∧ ¬q ∣ v) ∧
    (Nat.gcd v (p * q) = p ↔ p ∣ v ∧ ¬q ∣ v) ∧
    (Nat.gcd v (p * q) = 1 ∨ Nat.gcd v (p * q) = p ↔ ¬q ∣ v) ∧
    (Nat.gcd v (p * q) = 1 ∨ Nat.gcd v (p * q) = p ∨ Nat.gcd v (p * q) = q ↔
      ¬p ∣ v ∨ ¬q ∣ v) := by
  have hN : p * q = p ^ 1 * q ^ 1 := by simp
  obtain ⟨c, hc, e, he, hg⟩ := ICGGeneral.pq_gcd_rep hp hq (p * q) hN v
  have hpd : p ∣ v ↔ 1 ≤ c := by
    simpa using ICGGeneral.pq_dvd_iff_of_gcd hp hq hpq (p * q) hN
      (x := 1) (y := 0) le_rfl (by omega) hg
  have hqd : q ∣ v ↔ 1 ≤ e := by
    simpa using ICGGeneral.pq_dvd_iff_of_gcd hp hq hpq (p * q) hN
      (x := 0) (y := 1) (by omega) le_rfl hg
  have hN1 : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le]
  have hNp : p * q ≠ p := by nlinarith [hp.two_le, hq.two_le]
  have hNq : p * q ≠ q := by nlinarith [hp.two_le, hq.two_le]
  interval_cases c <;> interval_cases e <;>
    simp [hg, hpd, hqd, hp.ne_one, Ne.symm hp.ne_one, hq.ne_one, Ne.symm hq.ne_one, hpq, Ne.symm hpq, hN1, hNp, hNq]

end NarrowPQ

theorem check_PQGraphModels : NarrowSupplement.PQGraphModels := by
  intro p q hpq
  obtain ⟨hp, hq, hne, _hop, _hoq⟩ := hpq
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hc := ICGGeneral.coprime_pq hp hq hne
  let e := NarrowPQ.crt p q hc
  have hN1 : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le]
  have hNp : p * q ≠ p := by nlinarith [hp.two_le, hq.two_le]
  have hNq : p * q ≠ q := by nlinarith [hp.two_le, hq.two_le]
  refine ⟨⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩,
    ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩,
    ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩, ?_⟩
  · intro u v
    rw [GraphBridge.icg_adj_iff _ _ (by simp [hN1])]
    simp only [mem_singleton]
    rw [(NarrowPQ.gcd_classes hp hq hne (v - u).val).1,
      (NarrowPQ.coord_dvd p q hc u v).1, (NarrowPQ.coord_dvd p q hc u v).2]
    simp only [NarrowSupplement.unitaryProduct, SimpleGraph.fromRel_adj]
    dsimp only [e] at *
    aesop
  · intro u v
    rw [GraphBridge.icg_adj_iff _ _ (by simp [hNp])]
    simp only [mem_singleton]
    rw [(NarrowPQ.gcd_classes hp hq hne (v - u).val).2.1,
      (NarrowPQ.coord_dvd p q hc u v).1, (NarrowPQ.coord_dvd p q hc u v).2]
    simp only [NarrowSupplement.disjointCliques, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨huv, h⟩
      have h1 : (e v).1 = (e u).1 := h.elim Eq.symm id
      refine ⟨h1, ?_⟩
      intro h2
      apply huv
      exact Prod.ext h1.symm h2.symm
    · rintro ⟨h1, h2⟩
      refine ⟨?_, Or.inl h1.symm⟩
      intro huv; exact h2 (congrArg Prod.snd huv).symm
  · intro u v
    rw [GraphBridge.icg_adj_iff _ _ (by simp [hN1, hNp])]
    simp only [mem_insert, mem_singleton]
    rw [(NarrowPQ.gcd_classes hp hq hne (v - u).val).2.2.1,
      (NarrowPQ.coord_dvd p q hc u v).2]
    simp only [NarrowSupplement.completeParts, SimpleGraph.fromRel_adj]
    aesop
  · ext u v
    rw [GraphBridge.icg_adj_iff _ _ (by simp [hN1, hNp, hNq])]
    simp only [mem_insert, mem_singleton, SimpleGraph.top_adj]
    rw [(NarrowPQ.gcd_classes hp hq hne (v - u).val).2.2.2]
    rw [(NarrowPQ.coord_dvd p q hc u v).1, (NarrowPQ.coord_dvd p q hc u v).2]
    change (¬(e v).1 = (e u).1 ∨ ¬(e v).2 = (e u).2) ↔ u ≠ v
    constructor
    · rintro (h | h) huv
      · exact h (congrArg (fun w => (e w).1) huv).symm
      · exact h (congrArg (fun w => (e w).2) huv).symm
    · intro hne
      by_contra hn
      push Not at hn
      apply hne
      apply e.injective
      exact Prod.ext hn.1.symm hn.2.symm

#print axioms check_PQGraphModels
end CodexPaper1
