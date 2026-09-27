# Mapping: Lean model and C code

The C code is `src/libgit2/blame_git.c` at commit `3cbd497e5` (branch
[`exp/repo-blame`](https://github.com/EllianCarlos/libgit2/tree/exp/repo-blame) of EllianCarlos/libgit2). The
line numbers are for that commit. The Lean files are in
`lean/RepoblameProof/`.

"Exact" means that the Lean definition does the same computation, step by
step, as the C code (the replay compares them on traces). "Abstract"
means that the Lean model has a parameter in place of the C code; the
reference and repoblame use the same parameter, because repoblame does
not change that code.

## What repoblame changes

`git diff 1726b7074..3cbd497e5`, in a clone of that branch, changes only these
parts of the behaviour. All other changes are timers and counters
(`GIT_BLAME_PROFILE`, `cache_counts`), which do not change results.

1. `find_move_in_parent`: with a cache, a line filter of the parent blob,
   and a skip of each entry that the filter proves cannot move there.
2. `find_copy_in_parent`: with a cache, the list of sources comes from
   `blame_cache_sources` (not from `diff_copy_sources`), and the search
   is `find_best_copies_in_list` (not `find_best_copies_in_diff`).
3. `blame_cache_*`: the shared, thread-safe map of source lists.
4. `git_blame_file_cached` in `blame.c`: sets `blame->cache`.
   `git_blame_file` calls it with `NULL`, so the reference path is the
   same code with `blame->cache == NULL`.

## Table

| Lean (file: definition) | C (function, lines) | Kind | Notes |
|---|---|---|---|
| Basic: `LineView.key` | `blame_line_hash` 1408-1417 | abstract | The hash of a line without its newline. The model needs only: equal lines give equal keys (a function). |
| Basic: `LineView.alnum`, `asum`, `escore` | `blame_entry_score` 1184-1204; the per-line scores of `blame_hash_lines` 1482-1533 and `blame_entry_lines_init` 1602-1642 | exact | 1 plus the ASCII letters and digits. The newline is not a letter, so the per-line sums agree. |
| Basic: `Region`, `Region.Valid` | `handle_split_cb` 1288-1301, `handle_split` 1254-1273, `trim_common_tail` 516-538 | abstract (hypothesis `DiffValid`) | A region is one `handle_split` call with `tlno < same` (entry-relative `tlno`, blob line `plno`, length `same - tlno`). |
| Basic: `better` | `copy_split_if_better` 1215-1234 | exact | A later split with the same score wins. |
| Basic: `potOf`, `bestInBlob` | `find_copy_in_blob` 1311-1343 with `handle_split` | exact (given the regions) | The fold over the regions in diff order. |
| Filter: `pairItems`, `lineItems`, `items`, `lineScoreMin` | `blame_filter_build` 1536-1593, `BLAME_FILTER_LINE_SCORE` | exact | A single line only when `1 + score > 16`; every adjacent pair. The removal of duplicates does not change membership. |
| Filter: `FilterImpl.noFalseNeg` | `blame_filter_set` 1445-1455, `blame_filter_test` 1457-1469 | proved for `bloom` | `bloom` is proved for any probe function. |
| Filter: `mix`, `cEnc`, `cProbes`, `cSize`, `cBloom` | `blame_mix` 1397-1405, `blame_item_line` 1419-1422, `blame_item_pair` 1424-1427, `blame_filter_bit` 1430-1433, `blame_filter_set`, size rule in `blame_filter_build` | exact (bit for bit) | Used by the replay. The replay checks that the Lean and C decisions are the same. |
| Bound: `scanStep`, `scanHit`, `scan`, `canMatch` | `blame_source_can_match` 1662-1692 | exact | The early `return true` for `threshold < 16`, the run, and the two tests. |
| Select: `hi`, `accept` | `find_copy_in_parent` 2484-2603 (the test `score <= threshold → continue`) | exact | The caller uses the best split only when it scores above the threshold. |
| Select: `refFold` | `find_best_copies_in_diff` 1931-1992 | exact | Per candidate; the C loop is source-major, see `foldl_map_comm`. |
| Select: `OSt`, `bar`, `optStep`, `optFold` | `find_best_copies_in_list` 2275-2398 | exact | `c->split`, `best[j]`, the bar (`best[j] - 1` when `best[j] > threshold`), the skip, the update of `best[j]`. |
| Select: `foldl_map_comm` | the loops `for i (sources) { for j (candidates) }` in both functions | proved | Each candidate has its own state. |
| Blame: `Repo.deltas`, `Repo.oldSide`, `Repo.unmodFlag` | `diff_copy_sources` 1853-1884, `is_copy_source` 1891-1902 | abstract | The tree diff with the flag `GIT_DIFF_INCLUDE_UNMODIFIED`; the other diff options are constants. |
| Blame: `CKey`, `keyOf` | the key string in `blame_cache_sources` 2150-2237 | exact | "commit parent u/m f/n". |
| Blame: `mkSrc`, `canon`, `buildC`, `buildC_eq_canon` | `blame_source_list_build` 2061-2141 | exact (given the diff) | `is_copy_source(delta, NULL)`; a filter when "f" and the blob is at most `GIT_XDIFF_MAX_SIZE`; the salt is the first 8 bytes of the blob id. |
| Blame: `refSrc`, `refSources` | `diff_copy_sources` + `is_copy_source(delta, porigin)` | exact | |
| Blame: `filterPo`, `notPo` | `if (porigin && !strcmp(s->path, porigin->path)) continue;` in `find_best_copies_in_list` | exact | |
| Blame: `refSel`, `optSel`, `pruneSrc` | `find_best_copies_in_diff`, `find_best_copies_in_list` | exact | `prune && s->filtered` is `s.filt = some _`. |
| Blame: `refK`, `optK` | `blame->cache == NULL` or not | exact | |
| Blame: `pruneMove`, `moveLoop` | `find_move_in_parent` 1704-1805 | exact loop, abstract `split_blame` | The loop continues at the same entry after a split, as the C code does with `e`. |
| Blame: `moveAll` | the move part of `pass_blame` 2605-2757 | exact | `find_last_in_target` (return 1), `fill_origin_blob` (no blob: return 0). |
| Blame: `cands`, `rounds`, `copyOne`, `copyAll` | `add_copy_candidate` 1816-1832, `find_copy_in_parent`, the copy part of `pass_blame` | exact loop, abstract `split_blame` | `FileOps.applyCopies` is `split_blame` and `add_copy_candidate` for the parts that are left. |
| Blame: `FileOps.passParents` | `find_origin`, `find_rename`, `pass_whole_blame`, `pass_blame_to_parent` | abstract | Not changed by repoblame. |
| Blame: `passBlame`, `markGuilty`, `blame` | `pass_blame`, `git_blame__like_git` 2785-2840 | exact structure | `FileOps.coalesce` is `coalesce`. |
| Cache: `Prog`, `runPure` | a blame as a program that asks for source lists | model | The reference answers with the canonical list. |
| Cache: `Slot`, `Cache`, `lookup`, `publish`, `removeKey` | `blame_source_list` (`ready`), `blame_source_listmap` | model | One entry per key. |
| Cache: `Step.hit` | `blame_cache_sources`: a ready list is found (under the lock) | model | |
| Cache: `Step.miss` | the placeholder is put in the map (under the lock) | model | |
| Cache: (no step for a job that finds `building`) | `git_cond_wait` | model | A waiting blame does not move. |
| Cache: `Step.done` | the list is made without the lock, then `ready = true` and `git_cond_broadcast` (under the lock) | model | |
| Cache: `Step.fail` | a failed build removes the placeholder; the blame returns an error | model | |
| Cache: `Step.evict` | `blame_cache_evict` 2033-2054 | model (more general) | The model lets eviction remove any entries; the C code removes only ready lists that no blame uses. |
| Cache: the value that a job holds after `hit`/`done` | `refcount`, `blame_cache_release` 2239-2246 | model | A list in use is not freed. The model copies the value into the job. |

## What the mapping does not cover

- Error paths. The model has no errors (except `Step.fail`). On an error,
  the reference and repoblame can differ: the reference reads every
  source blob (`make_source_origin`) and runs every xdiff, so a missing
  blob or an entry above `GIT_XDIFF_MAX_SIZE` (about 1 GB) stops the
  reference with an error, while repoblame can skip that source and end
  without an error. On runs without errors, the theorems apply.
- Memory safety, the mutex and the condition variable themselves, the
  LRU order, and the counters.
- The base port (per-file blame against git). It is tested (317,573
  lines in the earlier work, and the tests here), not proved.
