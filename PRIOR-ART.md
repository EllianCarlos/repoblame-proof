# Prior art and tool survey for repoblame

Scope: public sources only. Checked 2026-09-26.

## Bottom line

repoblame extends libgit2 blame with git's copy/move detection (`-M`,
`-C`, `-C -C`, `-C -C -C`, and a numeric threshold), then blames a whole
repository in one process. It shares two caches across files and threads:
a per-(commit, parent) tree-diff cache of copy-source candidates, and a
per-blob Bloom filter over line hashes and adjacent-line-pair hashes. The
filter bounds the best possible xdiff split score for a candidate before
running xdiff, so xdiff calls can be skipped by branch and bound, with no
false negatives. The claim is exact equivalence to `git blame -C<num>`,
measured on real repositories.

No public tool found in this survey combines all three of: (1) real
cross-file copy/move detection matching git's own `-C`/`-M` algorithm,
(2) work sharing across many files in one whole-repository blame run, and
(3) a bound-based pruning step with a no-false-negative argument. Most
tools have at most one of these.

- **libgit2** defines flags for cross-file copy/move detection
  (`GIT_BLAME_TRACK_COPIES_*`), but its own header says they are "not yet
  implemented." repoblame implements this git-2.0-era feature in libgit2.
- **Git's own changed-path Bloom filters** (since 2.27, wired into
  `blame.c` by Derrick Stolee) are a real, shipped, similar-sounding
  feature, but they prune a different search: skipping whole commits that
  provably did not touch a *path*, in the ordinary first-parent walk.
  Git's own commit message says the filter is "explicitly disabled" the
  moment `-C` is used, because `-C`'s candidate set is not path-limited.
  repoblame's filter instead bounds a *content* similarity score (line
  hashes) between a blame chunk and a candidate source blob, used
  precisely during the `-C`/`-M` search that git's own filter exits from.
- **JGit's `BlameGenerator`** follows whole-file renames only; its javadoc
  says this "is not the same as copy/move detection as implemented by the
  C implementation's of `git blame -M -C`." It blames one file per
  instance; its optional cache is read-only and populated externally.
- **Hercules, git-of-theseus, git-truck, git-fame** compute line history
  across many or all files (so they share the "walk the whole repo" idea),
  but none of their public documentation claims cross-file copy/move
  detection matching git, and none claims exact equivalence to `git
  blame` output.
- SZZ-family tools (PyDriller, pySZZ_v2, SZZ Unleashed) call real
  `git blame`/JGit blame per file per commit range, inheriting whatever
  the underlying engine does, but add no cross-file sharing or pruning of
  their own beyond a timeout guard.

## Table

| Tool / work | (a) cross-file copy/move like `-C` | (b) shares work across files | (c) claims equivalence to git blame | Citation |
|---|---|---|---|---|
| Hercules (src-d/hercules) | Not documented | Yes — single DAG pass, incremental blame, multiple analyses per run | No — claims parity with git-of-theseus only | github.com/src-d/hercules |
| git-of-theseus (erikbern) | Not documented | Not documented | No | github.com/erikbern/git-of-theseus |
| gitoxide `gix-blame` | No — whole-file rename following only | No — one file per `blame::file()` call | Not claimed | github.com/GitoxideLabs/gitoxide/tree/main/gix-blame |
| git core `blame.c`/`builtin/blame.c` | Yes (the reference implementation) | Partial — Bloom filters share commit-graph data, off under `-C` | N/A (reference) | github.com/git/git, commit `0906ac2b54b6` |
| git changed-path Bloom filters | No — unrelated feature | Yes, but only for skipping commits not touching one path; off under `-C` | N/A | commit `0906ac2b54b6`; git-scm.com/docs/git-commit-graph |
| libgit2 `blame.h` flags | No — "not yet implemented and reserved for future use" | No | No | github.com/libgit2/libgit2 include/git2/blame.h |
| JGit `BlameGenerator` | No — explicitly disclaimed vs `-M -C` | No — one file per instance; cache is read-only, externally filled | No | jgit BlameGenerator.java |
| PyDriller | Delegates to underlying git/GitPython | Not documented | Not verified | pydriller.readthedocs.io |
| pySZZ_v2 | Yes, passes `-C`/`-M` to GitPython `blame_incremental` | No — one call per file/commit, timeout guard only | Implicit (calls real git blame) | github.com/grosa1/pyszz_v2 |
| SZZ Unleashed | Unverified — uses JGit, rename setting unstated | No | Not claimed | github.com/wogscpar/SZZUnleashed |
| git-fame | Yes, passes user's `-M`/`-C` to `git blame` | No — parallel per-file threads only | Implicit | github.com/casperdcl/git-fame |
| git-truck | Not documented | Not documented (some local caching, unstated scope) | Not documented | github.com/git-truck/git-truck |
| World of Code | Not verified; no line-level blame found | Yes, at blob/commit level, huge cross-repo dedup | No | DOI 10.1109/msr.2019.00031 |
| Software Heritage provenance | Not verified this session; believed blob-level | Yes, at content-address level, not line level | No | DOI 10.1007/s10664-020-09828-5 |
| cregit | No — application, not a blame engine; drives per-file `git blame -C100` | No — per-file driver script | N/A (consumer) | DOI 10.1007/s10664-019-09704-x |
| diffcore-rename (git core) | N/A — separate tree-rename code path from blame's own copy search | N/A | N/A | github.com/git/git diffcore-rename.c |

## Notes, with what was verified and what was not

**Hercules / burndown.** Verified from the README (github.com/src-d/hercules):
runs "a Directed Acyclic Graph (DAG) of analysis tasks over the full commit
history," with burndown computed by "a custom RB tree tracking algorithm,"
incrementally, in one pass. No mention of cross-file copy/move detection.
Its only equivalence claim is against git-of-theseus, not `git blame`. No
peer-reviewed paper for the blame/burndown algorithm was found; the linked
blog (`blog.sourced.tech`) no longer resolves. A related, citable paper
from the same team covers their dataset, not the algorithm: Markovtsev &
Long, "Public git archive," MSR 2018, DOI 10.1145/3196398.3196464.

**git-of-theseus.** README (github.com/erikbern/git-of-theseus) gives no
detail on copy/move handling, caching, or blame equivalence. Not verified
beyond the README.

**gitoxide `gix-blame`.** Verified from CHANGELOG.md and `src/lib.rs`.
Implemented: whole-file rename following (v0.3.0), multi-range blame
within one file, commit-graph traversal shortcuts. No entry mentions
`-C`/`-M`-style cross-file detection; the public API takes one file per
call with no shared cache across files.

**git's own blame internals.** Verified from `builtin/blame.c`/`blame.c`.
`-C`/`-M` are implemented by `find_copy_in_parent`, `find_copy_in_blob`,
`find_move_in_parent`: nested loops (every changed file pair x every blame
entry) with no bound comparable to a Bloom-filter bound. The file's only
complexity comment is for an unrelated function, `fuzzy_find_matching_lines`
("O(n log n) in the typical case and O(n^2) in a pathological case").
Git's major blame speedup instead was a data-structure rewrite: David
Kastrup, "blame: large-scale performance rewrite," commit `7e6ac6e4`
(2014-04-26) — old code kept one sorted list so "run time grew
quadratically with the number of chunks"; the rewrite (per-origin queues,
a priority queue by commit date) gave "a speedup by a factor of 3 or
more." Orthogonal to Bloom filters. Barret Rhoden separately added
`--ignore-rev`/`--ignore-revs-file` (commit `ae3f36de`, 2019-05-15), for
skipping reformatting/rename-only commits — unrelated to copy detection.

**Changed-path Bloom filters vs. repoblame's filter (key distinction).**
Verified from commit `0906ac2b54b69eb98c448ad0072be1a1c355fbc4`, "blame:
use changed-path Bloom filters" (Derrick Stolee, 2020-04-16), and
git-scm.com/docs/git-commit-graph. Git's filter answers "did commit X
touch path P?" — a per-commit Bloom filter over changed paths, consulted
in `find_origin()` before a first-parent tree diff, mainly built for
`git log -- <path>`-style queries. The commit message explains it is
disabled for `-C`, since `-C` must consider content from files *other*
than the blamed path. Measured effect on Linux-kernel files (best of 5):
`arch/x86/kernel/topology.c` 0.83s to 0.24s; `kernel/time/time.c` 0.72s to
0.24s; `tools/perf/ui/stdio/hist.c` 0.27s to 0.11s; `MAINTAINERS` 20.1s to
18.0s. The author states remaining cost is dominated by line-level diff
computation, untouched by this change, and calls out `-C` as future work.
repoblame's filter answers a different question — "could file B contain a
content-matching run of lines for this blame chunk, well enough to beat
the current best score?" — via a per-blob Bloom filter over line hashes
and adjacent-pair hashes, used precisely inside the `-C`/`-M` search that
git's own path filter exits early from. This is the gap the 2020 commit
message leaves open.

**libgit2.** Verified from `include/git2/blame.h`: all four
`GIT_BLAME_TRACK_COPIES_*` flags (`SAME_FILE`=`-M`, `SAME_COMMIT_MOVES`=
`-C`, `SAME_COMMIT_COPIES`=`-CC`, `ANY_COMMIT_COPIES`=`-CCC`) carry the
comment "This is not yet implemented and reserved for future use." Issue
#2032 ("Blame hunk's orig_commit_id," 2014, closed) shows a user confused
by docs describing behavior that isn't implemented. No other open issue
about the missing feature was found.

**JGit `BlameGenerator`.** Verified from the source file itself. Javadoc:
whole-file rename following uses "the standard FollowFilter behavior used
by RevWalk (which matches `git log --follow`" and explicitly "is not the
same as copy/move detection as implemented by the C implementation's of
`git blame -M -C`." An instance "can only be used once. To blame multiple
files the application must create a new BlameGenerator," and "is not
thread-safe." An optional `BlameCache` (since JGit 7.2) is consumed, not
populated — "This generator will not populate it, just consume it" — so
sharing across files is the caller's job. JGit's `ChangedPathTreeFilter`
(`setUseCommitGraphOptimizations`) is JGit's analog of git's changed-path
Bloom filter, with the same path-only scope.

**SZZ-family tools.** PyDriller's docs list Git/blame and diff-algorithm
pages, but I could not confirm from the fetched page whether its wrapper
exposes `-C`/`-M`. pySZZ_v2 (github.com/grosa1/pyszz_v2, backing DOI
10.1016/j.jss.2023.111729): verified from `szz/core/abstract_szz.py` —
calls GitPython's `blame_incremental(**kwargs, rev=rev, L=mod_line_ranges,
file=file_path)`, building `kwargs['M']` for `-M` and `kwargs['C']` for
`-C`/`-C -C`/`-C -C -C` from a `DetectLineMoved` enum. Real git `-C`/`-M`
behavior, but strictly per-file, per-call; only a 1-hour timeout guard, no
cross-file cache. SZZ Unleashed (github.com/wogscpar/SZZUnleashed): README
says it "uses JGIT to parse a git repository" and "tries to use as many
cores as possible during runtime" (parallelism, not sharing); it does not
state whether JGit's rename-following is enabled. I found no distinct
public tool named "V-SZZ"; pySZZ_v2 lists AG-SZZ, L-SZZ, R-SZZ, MA-SZZ,
RA-SZZ, PyDriller-SZZ, A-SZZ, DU-SZZ, REV-SZZ, citing Rosa et al., JSS 202
(2023), DOI 10.1016/j.jss.2023.111729.

**cregit.** Verified bibliographic record only (Crossref): German, Adams,
Stewart, EMSE 24(4), pp. 2725-2763, 2019, DOI 10.1007/s10664-019-09704-x.
Full text is paywalled (link.springer.com redirects to an IdP login); not
bypassed, so I cannot quote the paper's own cost statements. The public
repo (github.com/cregit/cregit) shows a Perl driver (`blameRepoFiles.pl`)
invoking blame per file, with a TODO "create a driver program for
processing an entire repository" — consistent with a per-file, non-shared
design.

**Other line-history / provenance research.**
LHDiff (Asaduzzaman, Roy, Schneider, Di Penta, ICSM 2013, DOI
10.1109/icsm.2013.78) and CodeShovel (Grund, Chowdhury, Bradley, Hall,
Holmes, ICSE 2021, DOI 10.1109/icse43902.2021.00135): bibliographic
records only, full text not fetched, so cross-file/whole-repo scope is
not confirmed. I did not find a tool literally named "CodeTracker" this
session; the closest confirmed relative is Hasan, Tsantalis,
Alikhanifard, "Refactoring-Aware Block Tracking in Commit History," IEEE
TSE 50(12), 2024, DOI 10.1109/tse.2024.3484586 (refactoring-aware, not
git's copy/move sense, no git-blame-equivalence claim). World of Code (Ma
et al., MSR 2019, DOI 10.1109/msr.2019.00031; EMSE 2021, DOI
10.1007/s10664-020-09905-9): a deduplicated cross-repository object
graph, at commit/blob level, built for mining, not line-exact blame;
papers not fetched in full, so this is provisional. Software Heritage
provenance (Rousseau, Di Cosmo, Zacchiroli, EMSE 2020, DOI
10.1007/s10664-020-09828-5): announcement page and PDF were unreachable
(404/bot-blocked) this session; based on the title and Software
Heritage's known Merkle-DAG design, this is believed to be blob-level, not
line-level, but this is *not verified from the paper text* and should be
checked before being relied on. git-fame (github.com/casperdcl/git-fame):
verified from the README — `-M`/`-C` are real, off-by-default pass-through
flags to `git blame`, with a FAQ note that they "can increase accuracy,
but take longer to compute"; blame calls run in a thread pool (parallelism,
not shared/cached work). git-truck (github.com/git-truck/git-truck):
README/docs give no implementation detail on blame or `-C`/`-M`; only a
general note that first-time analysis is slower, implying unstated local
caching. No research paper for git-truck was found. I searched for
"hyperblame" and could not confirm it as a real, public, documented tool;
Mercurial's `fastannotate` extension (a plausible relative: a per-file
`linelog` cache reused across `hg annotate` calls on revisions of the
*same* file) could not be loaded from any mirror tried (404 or bot-block),
so this remains an open question, not an established fact.

**Bloom filters / bound-based pruning elsewhere.** Verified from
`diffcore-rename.c`: git's whole-tree rename/copy detector (a different
code path from blame's `find_copy_in_parent`) already culls candidates
before the expensive similarity estimate — an exact-match hashmap keyed
by blob OID, a basename shortcut ("over 76% of file renames in linux just
moved files to a different directory but kept the same basename"), and a
size-based bound in `estimate_similarity()` that rejects a pair from size
alone before reading content. None of this is a Bloom filter, and none of
it is reused by blame's own `-C`/`-M` search — the two code paths are
separate. For clone detection, SourcererCC (Sajnani et al., ICSE 2016, DOI
10.1145/2884781.2884877) is the closest well-known example of index-based
candidate pruning before an expensive comparison, using an inverted token
index rather than a Bloom filter; full text not fetched, noted only as a
positioning reference. A targeted search for "Bloom filter" plus
clone/near-duplicate detection did not surface a paper using Bloom filters
to bound a similarity score for pruning; the closest hits use Bloom
filters for plain set membership (exact-duplicate marking), not bounding
(e.g., DOI 10.1101/2022.10.12.511997, DOI 10.1109/cic.2016.042). The
seed-and-extend paradigm in sequence alignment is a plausible external
analogy for "cheap filter before expensive alignment," but no direct,
citable link to repoblame's technique was confirmed this session.

## Venue shape

- **Tool paper, MSR or ICSME tool track.** Fits the "one practical
  contribution to an existing tool" shape; both venues have a track for
  it. Risk: tool tracks often want broader usage evidence than one
  integration.
- **Methods section of a dataset or empirical-study paper** (e.g., a
  cregit-scale dataset, or a re-blame accuracy/impact study). Ties the
  contribution to a concrete downstream need and lets the exactness proof
  carry the "is this safe to use" argument. Risk: buries a systems
  contribution inside a paper whose main claim is empirical.
- **Short paper on exactness-preserving pruning for `git blame -C/-M`.**
  Sharpest framing of the actual novelty (the Bloom-filter bound plus
  branch-and-bound, contrasted with git's own changed-path Bloom filter,
  which the 2020 commit explicitly does not extend to `-C`). Risk: a
  short paper needs the Lean 4 equivalence proof to be complete or very
  clearly scoped, or reviewers will ask for it.

## References

- Hercules: github.com/src-d/hercules
- git-of-theseus: github.com/erikbern/git-of-theseus
- gitoxide `gix-blame`: github.com/GitoxideLabs/gitoxide/tree/main/gix-blame ; docs.rs/gix-blame
- git `builtin/blame.c` / `blame.c`: github.com/git/git
- git commit-graph docs: git-scm.com/docs/git-commit-graph
- "blame: use changed-path Bloom filters": github.com/git/git/commit/0906ac2b54b69eb98c448ad0072be1a1c355fbc4
- "blame: large-scale performance rewrite": commit `7e6ac6e4391caa0fc379cb699013d503380e4214`, github.com/git/git
- "blame: add the ability to ignore commits and their changes": commit `ae3f36dea16e51041c56ba9ed6b38380c8421816`, github.com/git/git
- `git blame` docs: git-scm.com/docs/git-blame
- `diffcore-rename.c`: github.com/git/git/blob/master/diffcore-rename.c
- libgit2 `blame.h`: github.com/libgit2/libgit2/blob/main/include/git2/blame.h
- libgit2 issue #2032: github.com/libgit2/libgit2/issues/2032
- JGit `BlameGenerator.java`: raw.githubusercontent.com/eclipse-jgit/jgit/master/org.eclipse.jgit/src/org/eclipse/jgit/blame/BlameGenerator.java
- PyDriller docs: pydriller.readthedocs.io
- pySZZ_v2: github.com/grosa1/pyszz_v2
- SZZ Unleashed: github.com/wogscpar/SZZUnleashed
- Rosa et al., JSS 202 (2023), DOI 10.1016/j.jss.2023.111729
- git-fame: github.com/casperdcl/git-fame
- git-truck: github.com/git-truck/git-truck
- German, Adams, Stewart, EMSE 24(4), 2019, DOI 10.1007/s10664-019-09704-x
- cregit repo: github.com/cregit/cregit
- Asaduzzaman et al., ICSM 2013, DOI 10.1109/icsm.2013.78
- Grund et al., ICSE 2021, DOI 10.1109/icse43902.2021.00135
- Hasan, Tsantalis, Alikhanifard, IEEE TSE 50(12), 2024, DOI 10.1109/tse.2024.3484586
- Ma et al., MSR 2019, DOI 10.1109/msr.2019.00031; EMSE 26(2), 2021, DOI 10.1007/s10664-020-09905-9
- Rousseau, Di Cosmo, Zacchiroli, EMSE 2020, DOI 10.1007/s10664-020-09828-5
- Sajnani et al., ICSE 2016, DOI 10.1145/2884781.2884877
- Markovtsev, Long, MSR 2018, DOI 10.1145/3196398.3196464

### Sources checked but not reachable this session

- lore.kernel.org/git — blocked by Anubis bot protection on every attempt.
- link.springer.com full text/PDF for the cregit paper — paywalled (IdP login redirect); not bypassed.
- Software Heritage provenance announcement page and PDF — 404 / unreachable.
- Mercurial wiki `FastAnnotateExtension` and `hgext/fastannotate` source — 404 on mirrors tried; Mercurial's own host blocked by Anubis.
- DuckDuckGo HTML search — blocked by an anti-bot image challenge every time; general web search otherwise relied on GitHub search APIs and Crossref.
