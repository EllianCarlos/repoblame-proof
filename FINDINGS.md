# repoblame: proof and tests (work log)

Status: IN PROGRESS. This file is updated after each step.

## Bottom line (so far)

- Proved in Lean 4.34.1 (core only, no Mathlib), no `sorry`, only the
  standard axioms `propext`, `Classical.choice`, `Quot.sound`
  (see `lean/axioms.txt`): the model of repoblame gives the same
  scoreboard as the model of the per-file blame, for each file, under
  any schedule of the files and threads.
- Tested: see the differential tests (next step).
- Assumed: the model matches the C code (see MAPPING.md), xdiff reports
  valid common runs, the mutex sections are atomic, no error occurs.

## Steps

1. 2026-09-26: Lean toolchain installed with elan (stable 4.34.1). No
   toolchain was present before.
2. Lean model and proofs: `lean/RepoblameProof/*.lean`, commit after
   `49494f8`.
