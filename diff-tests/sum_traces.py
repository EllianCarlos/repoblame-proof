#!/usr/bin/env python3
"""Sum the replay rows of trace_batch.sh: one total per run kind (n = no
cache, c = cache), for all modes except wC and for wC alone."""
import sys
from collections import defaultdict

tot = defaultdict(lambda: defaultdict(int))
cross = defaultdict(lambda: [0, 0])
repos = set()
msgs = defaultdict(int)
for fn in sys.argv[1:]:
    for line in open(fn):
        f = line.rstrip("\n").split("\t")
        if len(f) < 3:
            continue
        name, mode = f[0], f[1]
        repos.add(name)
        grp = "wC" if mode == "wC" else "other"
        if f[2].strip().startswith("!"):
            msgs[(grp, f[2].strip()[:40])] += 1
            continue
        if f[2] == "cross":
            kv = dict(x.split("=") for x in f[3:])
            cross[grp][0] += int(kv["ok"])
            cross[grp][1] += int(kv["bad"])
            continue
        kind = "n" if f[2].endswith("/n.trace") else "c"
        for x in f[3:]:
            k, v = x.split("=")
            tot[(grp, kind)][k] += int(v)
print("repos", len(repos))
for key in sorted(tot):
    print(key, " ".join("%s=%d" % kv for kv in tot[key].items()))
for g, (ok, bad) in sorted(cross.items()):
    print("cross", g, "ok=%d bad=%d" % (ok, bad))
for (g, m), n in sorted(msgs.items()):
    print("msg", g, n, m)
