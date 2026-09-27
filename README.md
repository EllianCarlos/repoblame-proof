# repoblame-proof

A Lean 4 proof, and differential tests, that **repoblame** gives the same
blame as per-file `git blame -C<num>`.

repoblame is a libgit2 experiment: it blames all files of a repository in
one process. The files share a cache of the copy search (for each commit
and parent, the list of source files and a line filter for each source).
The search skips a source when the filter proves that no copy from it can
score above the bar. The code is on branch `exp/repo-blame` of
[EllianCarlos/libgit2](https://github.com/EllianCarlos/libgit2)
([pull request #2](https://github.com/EllianCarlos/libgit2/pull/2)). The
proof is about commit `3cbd497e5`.

## Result

| | Result |
|---|---|
| Lean 4.34.1, core library only | builds; no `sorry`, no `admit`, no new axiom |
| Axioms of the main theorems | `propext`, `Classical.choice`, `Quot.sound` only |
| End-to-end tests: 231 repositories, 10 option sets | 0 of 2,652,560 line comparisons differ from the uncached blame |
| Uncached blame against git 2.55.0 | 0 of 663,140 lines differ |
| Thread stress: shuffled lists, 2 threads, 1-byte cache | 0 of 12,720 blames differ |
| Lean definitions replayed on C traces | 0 failures on 408,103 skip decisions and 61,636 copy searches |

The main theorems (`lean/RepoblameProof/Main.lean`):

- `repoblame_eq_reference`: for one file, repoblame gives the same
  scoreboard as the reference blame without a cache.
- `repoblame_any_schedule`: the same holds for many files and threads
  that share the cache, for any schedule, any eviction, and any failed
  build of a list.

Hypotheses:

1. `DiffValid`: xdiff reports runs of lines that are byte-equal in the two
   files. This is false with `-w`; the C code turns the filter off there.
2. The filter has no false negatives. This is proved for the C filter, for
   any hash function. Hash quality changes only the speed.

Not proved (see `FINDINGS.md`):

- that the Lean model matches the C code (`MAPPING.md` maps each
  definition to C lines; the trace replay tests it);
- the error paths (for example, a blob that cannot be read);
- memory safety of the C code;
- that libgit2 blame equals git (tested on 317,573 lines, not proved).

## Check the proof

Install Lean with [elan](https://github.com/leanprover/elan). Then:

    cd lean
    lake build
    lake env lean Axioms.lean

The last command prints the axioms of each main theorem.

## Run the differential tests

The tests need a build of libgit2 at `3cbd497e5`, and git.

1. Make a detached worktree of `exp/repo-blame` at `3cbd497e5` in
   `work/`, and build it out of tree in `work/build`.
2. Build the driver `diff-tests/rbdrive.c` against that build.
3. Make test repositories with `diff-tests/gen_repo.py` (seeded).
4. Run `diff-tests/run_diff.py <outdir> <repo>...`. It prints one TSV row
   for each repository and option set.

For the trace replay, apply `diff-tests/trace.patch` to a second worktree
(`work/build-trace`, logging only), then run `diff-tests/trace_batch.sh`.
`FINDINGS.md` gives the full method.

## Files

| File | Content |
|---|---|
| `FINDINGS.md` | results, theorem list, proof outline, method |
| `MAPPING.md` | each Lean definition and its C lines |
| `PRIOR-ART.md` | survey of related tools and papers |
| `lean/` | the Lean model and proof |
| `diff-tests/` | test generators, drivers, and recorded results |

## License

GPLv2 with the linking exception, the same as libgit2 (see `COPYING`).
`diff-tests/trace.patch` and `diff-tests/rbdrive.c` are derived from
libgit2.
