#!/bin/zsh
# Reproduce every check of PROOF.md section 7 (single core; about 4 minutes).
# Inputs not regenerated here: certificates/cm_S4.json, cm_S5.json (CaDiCaL, group_cm_sat.py),
# cm_S6.json (DLX exact cover, group_cm_dlx.py, 409 s).
set -e
cd "$(dirname "$0")"
D=..
echo "run_all start $(date -u +%Y-%m-%dT%H:%M:%SZ)"
python3 check_structure.py        > $D/logs/check_structure.log 2>&1 && tail -1 $D/logs/check_structure.log
python3 nonexistence.py           > $D/logs/nonexistence.log 2>&1 && tail -1 $D/logs/nonexistence.log
python3 check_triangle_indep.py   > $D/logs/check_triangle_indep.log 2>&1 && tail -1 $D/logs/check_triangle_indep.log
python3 check_proof_rho.py        > $D/logs/check_proof_rho.log 2>&1 && tail -1 $D/logs/check_proof_rho.log
python3 check_parities.py         > $D/logs/check_parities.log 2>&1 && head -1 $D/logs/check_parities.log
python3 write_rho.py              > $D/logs/write_rho.log 2>&1
: > $D/logs/certificates.log
for spec in "B 6 2" "B 7 3" "B 1 all" "B 4 all" "B 5 all" "B 6 all" "PB 1 all" "PB 4 all" "PB 5 all" "PB 6 all"; do
  set -- ${=spec}
  python3 construct.py $1 $2 $3 proof $D/certificates >> $D/logs/certificates.log 2>&1
  tag=$([ "$3" = all ] && echo all || echo rank$3)
  python3 verify_cm.py $D/certificates/cm_$1$2_$tag.txt $1 $2 $3 >> $D/logs/certificates.log 2>&1
done
for spec in "B 6 2" "B 7 3"; do
  set -- ${=spec}
  python3 construct.py $1 $2 $3 generic $D/certificates/alt >> $D/logs/certificates.log 2>&1
  python3 verify_cm.py $D/certificates/alt/cm_$1$2_rank$3.txt $1 $2 $3 >> $D/logs/certificates.log 2>&1
done
grep -c VERIFIED $D/logs/certificates.log
# In the public release the Lean file is lean/Research/BrauerCMCore.lean at the repository root, and the
# source paper (src/) is not redistributed; logs/hashes.txt records the hashes of the original working run.
(cd $D && shasum -a 256 certificates/*.txt certificates/*.json certificates/alt/*.txt code/*.py code/*.sh CONTRACT.md > logs/hashes-release.txt)
echo "run_all end $(date -u +%Y-%m-%dT%H:%M:%SZ)"
