import Research.Backfill.Paper7.ChallengeV2
import Research.Backfill.Paper7.AlgebraicContracts
import Research.Backfill.Paper7.LegacyDumpContracts
import Research.Backfill.Paper7.LegacyEnumeration
import Research.Backfill.Paper7.LegacyTransfer

/-!
# Paper 7 V3 complete statement candidate entrypoint

The 38 existing mathematical contracts and primitives remain byte-identical in
ChallengeV2. New contracts live in BackfillPaper7.Challenge.Legacy and its Algebra
namespace. This file only assembles definitions; no paper target is proved.
See MANIFEST.json for exact contract names, source versions, coverage and remaining
static-review boundaries. No source is frozen; execution_ready is false.

B2's six-hash-bound historical leaf data are finite mathematical objects. Their
same-set/cardinality claims and A4 completeness are separate proof obligations.
No correctness of LAPACK, a C executable, or an unverified external table is assumed.
-/
