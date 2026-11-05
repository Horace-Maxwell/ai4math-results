# Lean package of Paper 7, version 2

The files of `lean/Research/Backfill/Paper7/` and the record of their builds. Version 2 of the paper does
not rest on the programs in `certificates/sun-graphs/code/`, which belong to version 1.

- `package-manifest.json`: the SHA-256 and the imports of every module of the package, the Lean toolchain,
  the Mathlib commit, the date of the frozen statement files and the entry point
  `Research.Backfill.Paper7.ClaudePaper7FinalPackage`, which restates the 58 frozen statements.
- The 31 statement and test files are the files frozen on 18 October 2026. 8 of the copies here are
  byte for byte the frozen files; the other 23 differ only in their `import` lines, which carry the prefix
  `Research.Backfill.Paper7.`. With the `import` lines removed, the SHA-256 hashes of all 31 agree.
  `frozen_files` in `package-manifest.json` gives the three hashes of each file.
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with
  Lean 4.34.1 and the pinned Mathlib. Builds A and B compiled and replayed the 1925 modules of the package
  from two empty directories; their 1925 `.olean` files are byte for byte identical
  (`olean_comparison_A_B`). The whole-project build compiled and replayed the 2841 modules of the
  repository from a third empty directory.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file and the compile and `leanchecker` log of
  every module of builds A and B. The whole-project logs are in `logs/clean-replay-v1.14.0-logs.tar.gz`.
  Logs of failed attempts have the suffix `.attempt1` and so on. The logs of the failed first attempt of
  build A were overwritten and are not here.

None of the builds ran in one piece, and `receipt.json` gives the details. Each failed attempt whose log is
kept stopped on a memory or file-read error or with a process that stopped. In the first pass of build A,
whose logs were overwritten, the log of one of the seven failed modules was read at the time and showed a
file-read error. No Lean check rejected a module. The modules concerned were run again from the same
sources, and all passed.

Comments in several modules written by Codex keep the words PENDING, blocked or NOT AN ACCEPTED COUNT from
the time they were written. The build records, not these comments, say what was accepted.

Paper 7 has not been checked with comparator or with the independent kernel nanoda. `leanchecker` replays
the proofs in the Lean kernel, and no other kernel has checked them.

Paths in these files are relative to the project in which the package was built; they are records, not
inputs of the build here.
