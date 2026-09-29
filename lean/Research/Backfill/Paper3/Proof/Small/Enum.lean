import Research.Backfill.Paper3.Proof.Small.Defs

/-!
# Small graphs: kernel enumeration on six labelled vertices (core Lean only)

Over all `2^15` edge masks on six vertices: exactly `70` are cubic, and every cubic mask has a
valid isomorphism certificate onto `K_{3,3}` or the prism (`allCert`). Both are evaluated by the
kernel (`decide +kernel`).
-/

set_option autoImplicit false

namespace P3Small

theorem regB_k33 : regB 6 k33Mask 3 = true := by decide +kernel

theorem regB_prism : regB 6 prismMask 3 = true := by decide +kernel

/-- There are `70` cubic edge masks on six vertices. -/
theorem countB_cubic6 : countB 32768 (fun c => regB 6 c 3) = 70 := by decide +kernel

/-- Every cubic edge mask on six vertices has a valid certificate in `certs6`. -/
theorem allCert_eq : allCert = true := by decide +kernel

end P3Small
