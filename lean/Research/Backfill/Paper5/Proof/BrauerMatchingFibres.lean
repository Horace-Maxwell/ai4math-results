import Research.Backfill.Paper5.Proof.BrauerMatchingLabels
import Research.Backfill.Paper5.Proof.BrauerMatchingTransport
import Research.Backfill.Paper5.Proof.BrauerJoin
import Research.Backfill.Paper5.Proof.GammaCompatibility

set_option autoImplicit false

namespace CodexPaper5.BrauerMatchingFibres

open BackfillPaper5

abbrev Fib (n r : ℕ) (F : HalfCounting.FreeSets n r) :=
  HalfFibreCounting.Fibre Challenge.Fam.B n r F.val

def special (n r : ℕ) (F : HalfCounting.FreeSets n r) : Prop :=
  ∃ j : Fin 3, F.val = (Challenge.triHalf n r j).1

def targetSet (n r : ℕ) : Set (Challenge.Half n) :=
  Challenge.Hr Challenge.Fam.B n r \
    {Challenge.triHalf n r 0, Challenge.triHalf n r 1, Challenge.triHalf n r 2}

abbrev Target (n r : ℕ) := {v : Challenge.Half n // v ∈ targetSet n r}

/-- Transport changes only the dependent free-set proof, keeping the actual Half. -/
def fibreTransport {n r : ℕ} {F G : HalfCounting.FreeSets n r} (h : F = G)
    (x : Fib n r F) : Fib n r G :=
  ⟨x.val, x.property.1, x.property.2.trans (congrArg Subtype.val h)⟩

def remainingEquivNonspecial (n r : ℕ) :
    BrauerMatchingLabels.RemainingLabels n r ≃
      BrauerMatchingTransport.Nonspecial (special n r) where
  toFun F := ⟨F.val, by
    rintro ⟨j, hj⟩
    exact F.property j hj⟩
  invFun F := ⟨F.val, by
    intro j hj
    exact F.property ⟨j, hj⟩⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl

/-- One choice per pair supplies both actual representatives and their common path. -/
theorem exists_pair_representatives (n r : ℕ) (hle : r ≤ n)
    (hpar : n % 2 = r % 2) (k : ℕ)
    (e : (Fin k × Bool) ≃ BrauerMatchingLabels.RemainingLabels n r)
    (hbound : ∀ i : Fin k,
      r + 2 * (((e (i, false)).val.val \ (e (i, true)).val.val).card) ≤ n) :
    ∃ p : ∀ a : Fin k × Bool, Fib n r (e a).val,
      ∀ i : Fin k, Challenge.Compat (p (i, false)).val (p (i, true)).val := by
  classical
  have hp : ∀ i : Fin k,
      ∃ v : Fib n r (e (i, false)).val,
        ∃ w : Fib n r (e (i, true)).val, Challenge.Compat v.val w.val := by
    intro i
    obtain ⟨v, hv, w, hw, hvF, hwF, hcompat⟩ :=
      BrauerJoin.exists_join_halves n r hle hpar (e (i, false)).val.val
        (e (i, true)).val.val (e (i, false)).val.property
        (e (i, true)).val.property (hbound i)
    exact ⟨⟨v, hv, hvF⟩, ⟨w, hw, hwF⟩, hcompat⟩
  choose v w hcompat using hp
  let p : ∀ a : Fin k × Bool, Fib n r (e a).val := fun
    | (i, false) => v i
    | (i, true) => w i
  exact ⟨p, hcompat⟩

open Classical in
/-- Special fibres use the prescribed triHalf; all others use the shared pair choice. -/
noncomputable def representative (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2) (k : ℕ)
    (e : (Fin k × Bool) ≃ BrauerMatchingLabels.RemainingLabels n r)
    (p : ∀ a : Fin k × Bool, Fib n r (e a).val)
    (F : HalfCounting.FreeSets n r) : Fib n r F :=
  if hs : special n r F then
    ⟨Challenge.triHalf n r hs.choose,
      BrauerTriangleBasics.triHalf_mem_hr n r hr hn hpar hs.choose,
      hs.choose_spec.symm⟩
  else
    let a : BrauerMatchingLabels.RemainingLabels n r :=
      ⟨F, fun j hj => hs ⟨j, hj⟩⟩
    fibreTransport (congrArg Subtype.val (e.apply_symm_apply a)) (p (e.symm a))

theorem representative_special (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2) (k : ℕ)
    (e : (Fin k × Bool) ≃ BrauerMatchingLabels.RemainingLabels n r)
    (p : ∀ a : Fin k × Bool, Fib n r (e a).val)
    (F : HalfCounting.FreeSets n r) (j : Fin 3)
    (hj : F.val = (Challenge.triHalf n r j).1) :
    (representative n r hr hn hpar k e p F).val = Challenge.triHalf n r j := by
  classical
  have hs : special n r F := ⟨j, hj⟩
  have hindex : hs.choose = j :=
    BrauerMatchingLabels.triHalf_free_injective n r hr hn (hs.choose_spec.symm.trans hj)
  unfold representative
  rw [dite_eq_left hs]
  change Challenge.triHalf n r hs.choose = Challenge.triHalf n r j
  exact congrArg (Challenge.triHalf n r) hindex

theorem representative_pair_val (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2) (k : ℕ)
    (e : (Fin k × Bool) ≃ BrauerMatchingLabels.RemainingLabels n r)
    (p : ∀ a : Fin k × Bool, Fib n r (e a).val) (a : Fin k × Bool) :
    (representative n r hr hn hpar k e p (e a).val).val = (p a).val := by
  classical
  have hs : ¬ special n r (e a).val := by
    rintro ⟨j, hj⟩
    exact (e a).property j hj
  unfold representative
  rw [dite_eq_right hs]
  change (p (e.symm (e a))).val = (p a).val
  rw [e.symm_apply_apply]

theorem exists_representatives (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hle : r ≤ n) (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2) (k : ℕ)
    (e : (Fin k × Bool) ≃ BrauerMatchingLabels.RemainingLabels n r)
    (hbound : ∀ i : Fin k,
      r + 2 * (((e (i, false)).val.val \ (e (i, true)).val.val).card) ≤ n) :
    ∃ rep : ∀ F : HalfCounting.FreeSets n r, Fib n r F,
      (∀ (F : HalfCounting.FreeSets n r) (j : Fin 3),
        F.val = (Challenge.triHalf n r j).1 → (rep F).val = Challenge.triHalf n r j) ∧
      ∀ i : Fin k,
        Challenge.Compat (rep (e (i, false)).val).val (rep (e (i, true)).val).val := by
  obtain ⟨p, hp⟩ := exists_pair_representatives n r hle hpar k e hbound
  let rep := representative n r hr hn hpar k e p
  refine ⟨rep, ?_, ?_⟩
  · exact representative_special n r hr hn hpar k e p
  · intro i
    change Challenge.Compat
      (representative n r hr hn hpar k e p (e (i, false)).val).val
      (representative n r hr hn hpar k e p (e (i, true)).val).val
    rw [representative_pair_val n r hr hn hpar k e p (i, false),
      representative_pair_val n r hr hn hpar k e p (i, true)]
    exact hp i

theorem fibre_card_odd (n r : ℕ) (hle : r ≤ n) (hpar : n % 2 = r % 2)
    (F : HalfCounting.FreeSets n r) : Odd (Nat.card (Fib n r F)) := by
  rw [HalfFibreCounting.card_fibre_B F.property hle hpar.symm]
  exact InvolutionCounting.odd_doubleFactorial_pred
    (HalfFibreCounting.even_complement hle hpar.symm)

theorem exists_fibre_pairing (n r : ℕ) (hle : r ≤ n) (hpar : n % 2 = r % 2)
    (rep : ∀ F : HalfCounting.FreeSets n r, Fib n r F)
    (F : HalfCounting.FreeSets n r) :
    ∃ q : BrauerMatchingTransport.Remainder (Fib n r) rep F →
        BrauerMatchingTransport.Remainder (Fib n r) rep F,
      Function.Involutive q ∧ ∀ a, q a ≠ a := by
  classical
  let : Fintype (Fib n r F) := Fintype.ofFinite (Fib n r F)
  let : Fintype (BrauerMatchingTransport.Remainder (Fib n r) rep F) :=
    Fintype.ofFinite (BrauerMatchingTransport.Remainder (Fib n r) rep F)
  have hc : Fintype.card (BrauerMatchingTransport.Remainder (Fib n r) rep F) =
      Nat.card (Fib n r F) - 1 := by
    calc
      _ = Fintype.card (Fib n r F) - 1 := by
        change Fintype.card {x : Fib n r F // x ≠ rep F} = _
        simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      _ = Nat.card (Fib n r F) - 1 :=
        congrArg (fun m : ℕ => m - 1) (Nat.card_eq_fintype_card (α := Fib n r F)).symm
  have heven : Even (Fintype.card
      (BrauerMatchingTransport.Remainder (Fib n r) rep F)) := by
    rw [hc, Nat.even_iff]
    have hodd := fibre_card_odd n r hle hpar F
    rw [Nat.odd_iff] at hodd
    omega
  exact DiagramRanksOccurring.exists_fixedPointFree_involution
    (BrauerMatchingTransport.Remainder (Fib n r) rep F) heven

theorem not_tri_iff (n r : ℕ) (v : Challenge.Half n) :
    v ∉ ({Challenge.triHalf n r 0, Challenge.triHalf n r 1,
      Challenge.triHalf n r 2} : Set (Challenge.Half n)) ↔
      ∀ j : Fin 3, v ≠ Challenge.triHalf n r j := by
  change (¬ (v = Challenge.triHalf n r 0 ∨ v = Challenge.triHalf n r 1 ∨
    v = Challenge.triHalf n r 2)) ↔ _
  constructor
  · intro h j hj
    fin_cases j
    · exact h (Or.inl hj)
    · exact h (Or.inr (Or.inl hj))
    · exact h (Or.inr (Or.inr hj))
  · intro h hv
    rcases hv with hv | hv | hv
    · exact h 0 hv
    · exact h 1 hv
    · exact h 2 hv

theorem target_mem_iff (n r : ℕ) (v : Challenge.Half n) :
    v ∈ targetSet n r ↔ v ∈ Challenge.Hr Challenge.Fam.B n r ∧
      ∀ j : Fin 3, v ≠ Challenge.triHalf n r j := by
  change (v ∈ Challenge.Hr Challenge.Fam.B n r ∧
    v ∉ ({Challenge.triHalf n r 0, Challenge.triHalf n r 1,
      Challenge.triHalf n r 2} : Set (Challenge.Half n))) ↔ _
  rw [not_tri_iff]

/-- Only the specified representative is removed from each special fibre. -/
theorem sigma_allowed_iff (n r : ℕ)
    (rep : ∀ F : HalfCounting.FreeSets n r, Fib n r F)
    (hrep : ∀ (F : HalfCounting.FreeSets n r) (j : Fin 3),
      F.val = (Challenge.triHalf n r j).1 → (rep F).val = Challenge.triHalf n r j)
    (z : Σ F : HalfCounting.FreeSets n r, Fib n r F) :
    (special n r z.1 → z.2 ≠ rep z.1) ↔
      ∀ j : Fin 3, z.2.val ≠ Challenge.triHalf n r j := by
  constructor
  · intro h j hj
    have hF : z.1.val = (Challenge.triHalf n r j).1 :=
      z.2.property.2.symm.trans (congrArg Prod.fst hj)
    exact h ⟨j, hF⟩ (Subtype.ext (hj.trans (hrep z.1 j hF).symm))
  · intro h hs heq
    obtain ⟨j, hF⟩ := hs
    exact h j ((congrArg Subtype.val heq).trans (hrep z.1 j hF))

def targetEquivAllowed (n r : ℕ)
    (rep : ∀ F : HalfCounting.FreeSets n r, Fib n r F)
    (hrep : ∀ (F : HalfCounting.FreeSets n r) (j : Fin 3),
      F.val = (Challenge.triHalf n r j).1 → (rep F).val = Challenge.triHalf n r j) :
    Target n r ≃ BrauerMatchingTransport.Allowed (Fib n r) rep (special n r) where
  toFun t := ⟨⟨⟨t.val.1, t.property.1.1⟩, ⟨t.val, t.property.1, rfl⟩⟩,
    (sigma_allowed_iff n r rep hrep _).mpr ((target_mem_iff n r t.val).mp t.property).2⟩
  invFun z := ⟨z.val.2.val, (target_mem_iff n r z.val.2.val).mpr
    ⟨z.val.2.property.1, (sigma_allowed_iff n r rep hrep z.val).mp z.property⟩⟩
  left_inv t := Subtype.ext rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨⟨F, hF⟩, ⟨⟨G, m⟩, hlegal, hGF⟩⟩, _hallowed⟩
    change G = F at hGF
    subst G
    rfl

#print axioms CodexPaper5.BrauerMatchingFibres.Fib
#print axioms CodexPaper5.BrauerMatchingFibres.special
#print axioms CodexPaper5.BrauerMatchingFibres.targetSet
#print axioms CodexPaper5.BrauerMatchingFibres.Target
#print axioms CodexPaper5.BrauerMatchingFibres.fibreTransport
#print axioms CodexPaper5.BrauerMatchingFibres.remainingEquivNonspecial
#print axioms CodexPaper5.BrauerMatchingFibres.exists_pair_representatives
#print axioms CodexPaper5.BrauerMatchingFibres.representative
#print axioms CodexPaper5.BrauerMatchingFibres.representative_special
#print axioms CodexPaper5.BrauerMatchingFibres.representative_pair_val
#print axioms CodexPaper5.BrauerMatchingFibres.exists_representatives
#print axioms CodexPaper5.BrauerMatchingFibres.fibre_card_odd
#print axioms CodexPaper5.BrauerMatchingFibres.exists_fibre_pairing
#print axioms CodexPaper5.BrauerMatchingFibres.not_tri_iff
#print axioms CodexPaper5.BrauerMatchingFibres.target_mem_iff
#print axioms CodexPaper5.BrauerMatchingFibres.sigma_allowed_iff
#print axioms CodexPaper5.BrauerMatchingFibres.targetEquivAllowed

end CodexPaper5.BrauerMatchingFibres
