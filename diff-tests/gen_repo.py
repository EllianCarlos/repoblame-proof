#!/usr/bin/env python3
"""Make a tiny random git repository that stresses the copy search.

usage: gen_repo.py <dir> <seed>

The repository has 5-12 text files and 15-40 commits.  The lines come
from a small vocabulary, so that many files have the same blocks (ties
between copy sources).  The operations: create a file from new lines or
from blocks of other files, insert or delete lines, copy or move a block
to another file, rename, delete, a "huge" commit that changes all
files, and a side branch with a merge.  Dates and names are fixed, so
the same seed gives the same repository.
"""
import os
import random
import subprocess
import sys

WORDS = ("alpha beta gamma delta epsilon zeta theta kappa lambda sigma omega "
         "value count index buffer length result status handler request "
         "response parse render update create delete source target").split()


def long_line(rng):
    n = rng.randint(3, 7)
    s = "_".join(rng.choice(WORDS) for _ in range(n))
    return rng.choice(["    ", "", "\t"]) + s + rng.choice([";", "();", " = 0;", ""])


def short_line(rng):
    return rng.choice(["}", "{", "", "  }", "x = 1;", "return;", "// -", "end"])


def make_vocab(rng):
    return [long_line(rng) for _ in range(40)] + [short_line(rng) for _ in range(8)]


def git(d, *args, env=None):
    subprocess.run(["git", "-C", d] + list(args), check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)


def main():
    d, seed = sys.argv[1], int(sys.argv[2])
    rng = random.Random(seed)
    vocab = make_vocab(rng)
    os.makedirs(d, exist_ok=True)
    git(d, "init", "-q", "-b", "main")
    files = {}   # path -> list of lines
    counter = [0]

    def newname():
        counter[0] += 1
        return "f%02d.txt" % counter[0]

    def block(lines):
        if not lines:
            return []
        a = rng.randrange(len(lines))
        b = min(len(lines), a + rng.randint(1, 6))
        return lines[a:b]

    def random_lines(n):
        return [rng.choice(vocab) for _ in range(n)]

    def write_all():
        for p in list(os.listdir(d)):
            if p.endswith(".txt"):
                os.remove(os.path.join(d, p))
        for p, ls in files.items():
            with open(os.path.join(d, p), "w") as f:
                text = "\n".join(ls)
                if ls and rng.random() < 0.9:
                    text += "\n"
                f.write(text)

    t = [1000000000]

    def commit(msg):
        write_all()
        t[0] += 3600
        env = dict(os.environ, GIT_AUTHOR_NAME="A%d" % rng.randint(1, 4),
                   GIT_AUTHOR_EMAIL="a@x", GIT_COMMITTER_NAME="C",
                   GIT_COMMITTER_EMAIL="c@x",
                   GIT_AUTHOR_DATE="%d +0000" % t[0],
                   GIT_COMMITTER_DATE="%d +0000" % t[0],
                   GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1")
        git(d, "add", "-A", env=env)
        git(d, "commit", "-q", "--allow-empty", "-m", msg, env=env)

    for _ in range(rng.randint(2, 4)):
        files[newname()] = random_lines(rng.randint(5, 25))
    commit("root")

    def op():
        k = rng.random()
        paths = sorted(files)
        if k < 0.12 and len(files) < 12:
            ls = []
            for _ in range(rng.randint(1, 4)):
                if paths and rng.random() < 0.7:
                    ls += block(files[rng.choice(paths)])
                else:
                    ls += random_lines(rng.randint(1, 5))
            files[newname()] = ls
        elif k < 0.35 and paths:
            p = rng.choice(paths)
            ls = files[p]
            i = rng.randint(0, len(ls))
            files[p] = ls[:i] + random_lines(rng.randint(1, 4)) + ls[i:]
        elif k < 0.45 and paths:
            p = rng.choice(paths)
            ls = files[p]
            if ls:
                i = rng.randrange(len(ls))
                files[p] = ls[:i] + ls[i + rng.randint(1, 3):]
        elif k < 0.62 and len(paths) >= 2:
            a, b = rng.sample(paths, 2)
            blk = block(files[a])
            i = rng.randint(0, len(files[b]))
            files[b] = files[b][:i] + blk + files[b][i:]
        elif k < 0.74 and len(paths) >= 2:
            a, b = rng.sample(paths, 2)
            la = files[a]
            if la:
                x = rng.randrange(len(la))
                y = min(len(la), x + rng.randint(1, 6))
                blk = la[x:y]
                files[a] = la[:x] + la[y:]
                i = rng.randint(0, len(files[b]))
                files[b] = files[b][:i] + blk + files[b][i:]
        elif k < 0.80 and paths:
            p = rng.choice(paths)
            ls = files[p]
            if len(ls) > 3:
                x = rng.randrange(len(ls))
                y = min(len(ls), x + rng.randint(1, 4))
                blk = ls[x:y]
                rest = ls[:x] + ls[y:]
                i = rng.randint(0, len(rest))
                files[p] = rest[:i] + blk + rest[i:]
        elif k < 0.86 and paths:
            p = rng.choice(paths)
            ls = files.pop(p)
            if rng.random() < 0.5 and ls:
                ls = ls[:]
                ls[rng.randrange(len(ls))] = rng.choice(vocab)
            files[newname()] = ls
        elif k < 0.90 and len(paths) > 2:
            files.pop(rng.choice(paths))
        elif k < 0.96 and paths:
            hdr = rng.choice(vocab)
            for p in paths:
                files[p] = [hdr] + files[p]
        else:
            for p in paths:
                ls = files[p]
                if ls:
                    i = rng.randrange(len(ls))
                    ls[i] = rng.choice(vocab)

    n = rng.randint(15, 40)
    merged = False
    for c in range(n):
        if not merged and c > 5 and rng.random() < 0.08:
            snap = {p: ls[:] for p, ls in files.items()}
            git(d, "checkout", "-q", "-b", "side")
            for _ in range(rng.randint(1, 3)):
                op()
                commit("side %d" % c)
            side = files
            git(d, "checkout", "-q", "main")
            files = snap
            op()
            commit("main %d" % c)
            env = dict(os.environ, GIT_AUTHOR_NAME="M", GIT_AUTHOR_EMAIL="m@x",
                       GIT_COMMITTER_NAME="M", GIT_COMMITTER_EMAIL="m@x",
                       GIT_AUTHOR_DATE="%d +0000" % (t[0] + 1),
                       GIT_COMMITTER_DATE="%d +0000" % (t[0] + 1),
                       GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_NOSYSTEM="1")
            r = subprocess.run(["git", "-C", d, "merge", "-q", "--no-edit", "side"],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
            if r.returncode != 0:
                # resolve: take the union of the two versions, file by file
                for p in set(side) | set(files):
                    if p in side and p in files:
                        files[p] = files[p] + [l for l in side[p] if l not in files[p]]
                    elif p in side:
                        files[p] = side[p]
                write_all()
                git(d, "add", "-A", env=env)
                git(d, "commit", "-q", "--no-edit", env=env)
            else:
                files = {}
                for p in os.listdir(d):
                    if p.endswith(".txt"):
                        with open(os.path.join(d, p)) as f:
                            files[p] = f.read().split("\n")
                        if files[p] and files[p][-1] == "":
                            files[p].pop()
            merged = True
            continue
        for _ in range(rng.randint(1, 3)):
            op()
        commit("c%d" % c)


if __name__ == "__main__":
    main()
