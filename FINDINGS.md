# repoblame: equivalence proof, tests, and assumptions

Subject: `repoblame`, the libgit2 branch `exp/repo-blame` at `3cbd497e5`
(`~/Projects/libgit2-work/libgit2-repoblame`) and the driver
`harness/repoblame.c`. The reference: the per-file blame of the same
library without a cache (`git_blame_file`, which is `blame->cache ==
NULL`). Git itself is a second reference for the tests only.

## Bottom line

**Proved (Lean 4.34.1, core only, no `sorry`, no new axiom).** In an
abstract model of the C code, repoblame gives the same scoreboard as the
reference per-file blame, for every file. This holds under every
schedule of the files and threads that share the cache (any order, any
interleaving at the mutex sections, any eviction, any failed build of a
list). There are two hypotheses: (1) xdiff reports common runs whose
lines are equal in the two files (`DiffValid`); (2) the filter has no
false negatives. (2) is proved for the C filter, for any hash function.
`#print axioms` of the main theorems gives only `propext`,
`Classical.choice` and `Quot.sound` (the standard axioms of Lean).

**Tested (the C code against the Lean model and against itself).**
- The Lean definitions, run on traces of the C code, give the same result
  as the C code at every decision point (see "Results").
- End to end, repoblame with a cache (1 thread; 2 threads with 2 passes
  and a shuffled list; a cache of 1 byte that removes every list, with 1
  and 2 threads) gives the same output as the reference. The reference
  gives the same output as git 2.55.0. This holds on the fixture and on
  random tiny repositories (see "Results").
- No violation of a proved property was found.

**Assumed (not proved).**
- The Lean model matches the C code. MAPPING.md maps each definition to
  C lines. The replay tests this on traces. It is not a proof about C.
- xdiff gives valid common runs (`DiffValid`). The replay checks it on
  every logged run. It is false with `-w`, but then the C code turns the
  filter off, so the proof does not need it there.
- The parts that repoblame does not change (`find_origin`, rename
  detection, `pass_blame_to_parent`, `split_blame`, `coalesce`) are the
  same functions in both semantics. They are parameters of the model.
- No errors. On error paths the two can differ (see "Error paths").
- The mutex sections are atomic, and a published list does not change.
  Memory safety of the C code is not in the model.
- The base port (per-file libgit2 blame = git) is tested (317,573 lines
  in the earlier work, and the runs here), not proved.

RESULTS_PLACEHOLDER

## Main theorem statements

File `lean/RepoblameProof/Main.lean`:

```lean
theorem repoblame_eq_reference (HD : DiffValid R) (FO : FileOps L O C P)
    (o2 : Ctx O C → List (Src L P FI.F)) (fuel : Nat) (sb : SB O) :
    runPure (oracle R FI) (blame R FI FO (optK R FI) fuel sb) =
    runPure o2 (blame R FI FO (refK R FI) fuel sb)

theorem repoblame_any_schedule (HD : DiffValid R) (FO : Nat → FileOps L O C P) (fuel : Nat)
    (sb0 : Nat → SB O) (cf : Conf (CKey C) (Ctx O C) (List (Src L P FI.F)) (SB O))
    (hrun : Star (Step (keyOf R) (buildC R FI))
      ⟨[], fun i => .run (blame R FI (FO i) (optK R FI) fuel (sb0 i))⟩ cf)
    (i : Nat) (v : SB O) (hfin : cf.jobs i = .run (.ret v)) :
    v = runPure (fun _ => []) (blame R FI (FO i) (refK R FI) fuel (sb0 i))
```

`R` is the repository: history, tree diffs, blobs, xdiff (an opaque
function), thresholds and flags. `FO` holds the unchanged per-file parts.
`optK` is the repoblame kernel (cache, filters, pruning). `refK` is the
reference kernel. The same `blame` walk runs with either kernel. `fuel`
bounds the loops; the theorems hold for every fuel.

The parts:

| Theorem | File | Statement |
|---|---|---|
| `FilterImpl.noFalseNeg` of `bloom` | Filter | For any probe function, an item that was put in the filter tests true. `cBloom` (the C filter, bit for bit) is an instance. |
| `canMatch_sound` | Bound | If a valid region of the entry lines against the source scores above `t`, `blame_source_can_match(t)` returns true. |
| `canMatch_false_le` | Bound | If it returns false, every valid region scores at most `t`. |
| `accept_optFold` | Select | When each skipped split scores at most its bar, the pruned fold and the reference fold of `copy_split_if_better` accept the same split. The tie rule (the last source with the highest score) is kept. |
| `optFold_noskip` | Select | Without a filter, the pruned fold is the reference fold. |
| `foldl_map_comm` | Select | The source-major loop is one fold per candidate. |
| `moveLoop_filter` | Main | The move search with the filter of the parent blob gives the same scoreboard as without it. |
| `buildC_eq_canon` | Blame | The list that `blame_source_list_build` makes is a function of the key (commit, parent, include-unmodified, filters) only. |
| `cache_sound` | Cache | In any run of the cache machine, a finished blame returns the value of its program under the canonical oracle. |
| `repoblame_eq_reference` | Main | The main theorem for one file. |
| `reference_oracle_free` | Main | The reference asks no question. |
| `repoblame_any_schedule` | Main | The main theorem for many files and threads. |

`#print axioms` (file `lean/axioms.txt`):

```
'RB.repoblame_eq_reference' depends on axioms: [propext, Classical.choice, Quot.sound]
'RB.repoblame_any_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
'RB.cache_sound' depends on axioms: [propext, Quot.sound]
'RB.canMatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RB.accept_optFold' depends on axioms: [propext, Quot.sound]
'RB.moveLoop_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
'RB.buildC_eq_canon' depends on axioms: [propext]
'RB.reference_oracle_free' depends on axioms: [propext, Quot.sound]
'RB.optFold_noskip' depends on axioms: [propext]
'RB.foldl_map_comm' depends on axioms: [propext, Quot.sound]
```

To check: `cd lean && lake build && lake env lean Axioms.lean`.

## How the proof goes

1. Bound (`canMatch_sound`). A region is a run of entry lines that are
   equal to consecutive source lines. So each adjacent pair of the run is
   an adjacent pair of the source, and each line is a source line. These
   are items of the filter, and the filter has no false negatives. The
   scan of `blame_source_can_match` reaches the end of the run with a run
   sum at least the score of the region, so it returns true.
2. Selection (`accept_optFold`). A simulation relation links the state
   of the reference fold and of the pruned fold: when the reference split
   is above the threshold, the two splits are equal; when it is not, the
   pruned split is not above the threshold either; and `best[j]` is the
   score of the pruned split. A skip happens only when the skipped split
   scores at most the bar. If the current best `b` is above the
   threshold, the bar is `b - 1`, so the skipped split scores below `b`
   and `copy_split_if_better` keeps `b` in the reference too. A split
   with the same score `b` is never skipped, so the later one wins in
   both (the tie rule). Otherwise the bar is the threshold, and a skipped
   split cannot become an accepted split.
3. Move filter (`moveLoop_filter`). A skipped entry has no split above
   the move threshold, so the reference goes to the next entry, too.
4. Cache (`cache_sound`). Each ready list in the map is the canonical
   list of its key (an invariant of every step). A blame that gets a list
   from the map gets the canonical list. So each job keeps the value that
   it has under the canonical oracle.
5. The walk (`blame_congr`). The walk is one definition with a kernel
   parameter. If the kernels agree on the move search and on the accepted
   splits, the walks agree. Steps 1-4 give that.

## What repoblame changes (from the C code)

`git diff 1726b7074..3cbd497e5` changes three behaviours. The rest is
timers and counters.

1. The copy source list comes from a shared map with the key
   "commit parent u|m f|n" (`blame_cache_sources`), not from a new tree
   diff (`diff_copy_sources`). The list keeps the file of `porigin`; the
   search skips it.
2. `find_best_copies_in_list` skips a (candidate, source) pair when the
   filter proves that no split of this source scores above the bar. The
   bar is the threshold, or `best - 1` when the candidate already has a
   split with `best > threshold`.
3. `find_move_in_parent` (only with a cache) makes a filter of the parent
   blob, and skips each entry that the filter proves cannot score above
   the move threshold.

About the "hopeless-move-search cache": the code has no cache of move
searches between calls. Commit `c88c86bfe` ("skip hopeless move searches
with a cache") makes one filter of the parent blob in each call of
`find_move_in_parent`, and only when a cache object exists. There is no
state between calls, so there is nothing to invalidate. The theorem
`moveLoop_filter` covers it.

## The filter: false positives and false negatives

The correctness does not depend on probability. Only the speed does.

- No false negatives, for these reasons. `blame_filter_set` and
  `blame_filter_test` use the same probes (a function of the item, the
  salt and `nbits`). A set never clears a bit. `salt` and `nbits` do not
  change after the build. A list becomes visible to other threads only
  after it is complete (`ready = true` under the mutex). The Lean proof
  holds for every probe function, so the quality of the hash does not
  matter.
- The line item is a function of the bytes of the line without its
  newline. Equal lines give equal items. Lines that xdiff matches are
  byte-equal (without `-w`), so they give equal items.
- Hash collisions (the 64-bit line hash, the item hash, the bit map, the
  cap of 2^31 bits) only give false positives: a source that cannot match
  gets an xdiff. The result does not change.
- The bound needs `DiffValid`. With `GIT_BLAME_IGNORE_WHITESPACE`, xdiff
  matches lines that differ in whitespace, so `DiffValid` is false. The
  replay shows this: all invalid regions come from `-w` runs. The C code
  does not use the filter with `-w` (`prune`, the `f/n` part of the key,
  and the move filter test the flag). So this is not a violation.
- A single line goes in the filter only when it scores above 16. For a
  bar below 16, `blame_source_can_match` returns true at once. The Lean
  model has the same guard, and the proof uses it.

## Error paths (a known difference; the theorems do not cover it)

The model has no errors. The reference reads the blob of every source
(`make_source_origin`) and runs xdiff for every pair; repoblame can skip
a pair. So a blob that cannot be read, or an entry above
`GIT_XDIFF_MAX_SIZE` (about 1 GB), can make the reference fail while
repoblame ends. (`blame_source_list_build` also reads every blob when it
makes filters, so the first case mostly fails in both.) This has no
effect on runs that end without an error.

## Differential tests: method

Tools (all in this repository):

- `work/` (ignored by git): two detached worktrees of `3cbd497e5`
  (`git worktree add --detach`), built out of tree. `work/build` is the
  unchanged code. `work/build-trace` has `diff-tests/trace.patch`
  (logging only, behind `RB_TRACE`; the traced outputs are equal to the
  untraced outputs).
- `diff-tests/rbdrive.c`: a copy of `harness/repoblame.c` with one more
  option, `-b BYTES` (the cache limit in bytes).
- `diff-tests/gen_repo.py`: random tiny repositories (seeded). They have
  blocks that many files share (ties between sources), copies, moves,
  renames, deletions, huge commits that change every file, and a merge.
  "wide" repositories have 15-30 files and new files made from many
  blocks (a small copy of the Playbook.java case).
- `diff-tests/run_diff.py`: end to end. For each option set: git, the
  reference (`rbdrive -n`), and four cache variants (`c1`: 1 thread;
  `c2`: 2 threads, 2 passes, shuffled list; `ev`: cache limit of 1 byte;
  `evj`: the same with 2 threads and the list reversed).
- `diff-tests/trace_batch.sh` and `lean/Replay.lean`: the C traces
  (without and with the cache) and the Lean replay. The replay checks:
  every region is valid (`DiffValid`); the bound holds at the tightest
  bar (`canMatch(score - 1) = true`); the Lean reference fold equals the
  split of `find_best_copies_in_diff`; the Lean pruned fold equals the
  split of `find_best_copies_in_list`; each Lean skip decision and bar
  equals the C decision and bar; the accepted splits are equal (the
  theorem instance); the move decisions agree; and the two runs of the
  same files have the same rounds and the same accepted splits.

Option sets: none, `-M`, `-C`, `-C100`, `-C -C`, `-C -C -C`,
`-C -C -C100`, `-C10`, `-M10`, `-w -C`.

## Novelty

See PRIOR-ART.md.

## Log

1. 2026-09-26 22:47: no Lean toolchain was present (only elan). Installed
   the stable toolchain 4.34.1 with elan (no Mathlib).
2. Lean model and proofs: commits `322ea2b`, `49494f8`, `f0255f7`.
3. Mapping and tests: commits `193a5f2`, `7df9766`.
4. `libgit2_tests -sblame` on `work/build`: 57 of 57 pass.
5. End-to-end batch (200 random repositories) and trace batch: see
   "Results".
