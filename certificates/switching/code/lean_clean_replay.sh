#!/bin/zsh
# Clean-directory replay of Research/SwitchingWalkProfile{,Audit}.lean (playbook 3.5 step 4).
# Fresh directory with only lakefile/manifest/toolchain + the two sources; .lake/packages symlinked
# to the dev project's cache (Mathlib oleans reused, no project oleans copied).
set -e
P=${P:?set P to the project root}
W=$P/work/round6/switching
export PATH=$P/work/toolchains/lean-4.33.1-darwin_aarch64/bin:$PATH
R=$W/lean/replay-$(date -u +%Y%m%dT%H%M%SZ)
mkdir -p $R/Research $R/.lake
cp $P/work/research-lean/lakefile.toml $P/work/research-lean/lake-manifest.json $P/work/research-lean/lean-toolchain $R/
cp $W/lean/SwitchingWalkProfile.lean $W/lean/SwitchingWalkProfileAudit.lean $R/Research/
printf 'import Research.SwitchingWalkProfile\nimport Research.SwitchingWalkProfileAudit\n' > $R/Research.lean
ln -s $P/work/research-lean/.lake/packages $R/.lake/packages
cd $R
echo "start $(date -u +%Y-%m-%dT%H:%M:%SZ)" > replay.log
echo "cwd $R" >> replay.log
echo "lean $(lean --version)" >> replay.log
echo "mathlib rev $(grep -A6 '"name": "mathlib"' lake-manifest.json | grep '"rev"')" >> replay.log
shasum -a 256 lakefile.toml lake-manifest.json lean-toolchain Research.lean Research/*.lean >> replay.log
set +e
lake build Research.SwitchingWalkProfile Research.SwitchingWalkProfileAudit > build.log 2>&1
echo "exit $?" >> replay.log
set -e
echo "end $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> replay.log
grep -c "depends on axioms" build.log >> replay.log || true
grep "depends on axioms" build.log | grep -vE "axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]" >> replay.log || echo "axioms: all within {propext, Classical.choice, Quot.sound}" >> replay.log
(cd $W/lean && shasum -c SHA256SUMS) >> replay.log 2>&1 || true
shasum -a 256 build.log >> replay.log
cat replay.log
