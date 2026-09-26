#!/usr/bin/env python3
"""End-to-end differential test of repoblame.

For each repository and each option set, blame every file at HEAD with:
  git    git blame --line-porcelain <opts> (the system git)
  ref    rbdrive -n          (git_blame_file, no cache: the reference)
  c1     rbdrive             (cache, 1 thread, list order)
  c2     rbdrive -j 2 -r 2   (cache, 2 threads, 2 passes, shuffled list)
  ev     rbdrive -b 1        (cache of 1 byte: every list is removed
                              when no blame uses it)
  evj    rbdrive -b 1 -j 2   (the same with 2 threads, reversed list)
Each output line is "<commit> <orig_line> <orig_path>" per final line.
The script compares every variant with ref (the claim of the proof) and
ref with git (the claim of the base port).

usage: run_diff.py <outdir> <repo>...   (prints one TSV row per repo/mode)
"""
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RB = os.path.join(HERE, "..", "work", "rbdrive")
MODES = {
    "none": [], "M": ["-M"], "C": ["-C"], "C100": ["-C100"],
    "CC": ["-C", "-C"], "CCC": ["-C", "-C", "-C"],
    "CCC100": ["-C", "-C", "-C100"], "C10": ["-C10"], "M10": ["-M10"],
    "wC": ["-w", "-C"],
}
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL="/dev/null",
               GIT_CONFIG_NOSYSTEM="1", LC_ALL="C")


def git_blame(repo, opts, path):
    out = subprocess.run(["git", "-C", repo, "blame", "--line-porcelain"] + opts +
                         ["HEAD", "--", path], capture_output=True, env=GIT_ENV)
    if out.returncode != 0:
        return None
    rows, sha, orig, fname = [], None, None, None
    for line in out.stdout.decode("utf-8", "replace").split("\n"):
        if line.startswith("\t"):
            rows.append("%s %s %s" % (sha, orig, fname))
        elif line.startswith("filename "):
            fname = line[9:]
        else:
            parts = line.split(" ")
            if len(parts) >= 3 and len(parts[0]) == 40 and all(c in "0123456789abcdef" for c in parts[0]):
                sha, orig = parts[0], parts[1]
    return rows


def run_rb(repo, opts, extra, items, outdir):
    os.makedirs(outdir, exist_ok=True)
    listf = os.path.join(outdir, "list.tsv")
    with open(listf, "w") as f:
        for idx, p in items:
            f.write("%s\t%s\n" % (idx, p))
    r = subprocess.run([RB] + opts + extra + ["-o", outdir, "-s", os.path.join(outdir, "stats.tsv"),
                        repo, "HEAD", listf], capture_output=True)
    res = {}
    for idx, _ in items:
        fn = os.path.join(outdir, "%s.txt" % idx)
        if os.path.exists(fn):
            with open(fn) as f:
                res[idx] = f.read().rstrip("\n").split("\n") if os.path.getsize(fn) else []
    return r.returncode, res


def main():
    outroot = sys.argv[1]
    for repo in sys.argv[2:]:
        name = os.path.basename(repo.rstrip("/"))
        files = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", "HEAD"],
                               capture_output=True, text=True, env=GIT_ENV).stdout.split()
        items = [(str(i), p) for i, p in enumerate(files)]
        rng = random.Random(name)
        for mode, opts in MODES.items():
            od = os.path.join(outroot, name, mode)
            gitres = {idx: git_blame(repo, opts, p) for idx, p in items}
            variants = {}
            rc_ref, variants["ref"] = run_rb(repo, opts, ["-n"], items, od + "/ref")
            _, variants["c1"] = run_rb(repo, opts, [], items, od + "/c1")
            sh = items[:]
            rng.shuffle(sh)
            _, variants["c2"] = run_rb(repo, opts, ["-j", "2", "-r", "2"], sh, od + "/c2")
            _, variants["ev"] = run_rb(repo, opts, ["-b", "1"], items, od + "/ev")
            _, variants["evj"] = run_rb(repo, opts, ["-b", "1", "-j", "2"], items[::-1], od + "/evj")
            ref = variants["ref"]
            lines = sum(len(v) for v in ref.values())
            diffs = {}
            for vn in ("c1", "c2", "ev", "evj"):
                bad = 0
                for idx, _ in items:
                    a, b = ref.get(idx), variants[vn].get(idx)
                    if a is None or b is None:
                        bad += 1 if a != b else 0
                    elif a != b:
                        bad += sum(1 for x, y in zip(a, b) if x != y) + abs(len(a) - len(b))
                diffs[vn] = bad
            gbad, gfiles = 0, 0
            for idx, _ in items:
                a, g = ref.get(idx), gitres[idx]
                if a is None or g is None:
                    if a != g:
                        gbad += 1
                        gfiles += 1
                    continue
                n = sum(1 for x, y in zip(a, g) if x != y) + abs(len(a) - len(g))
                if n:
                    gbad += n
                    gfiles += 1
            print("\t".join(str(x) for x in [name, mode, len(items), lines, diffs["c1"], diffs["c2"],
                                              diffs["ev"], diffs["evj"], gbad, gfiles]), flush=True)


if __name__ == "__main__":
    main()
