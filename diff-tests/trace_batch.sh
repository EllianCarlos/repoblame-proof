#!/bin/bash
# trace_batch.sh <out.tsv> <repo>...: trace the C code without and with
# the cache for each mode, and replay both traces with the Lean model.
cd "$(dirname "$0")"
out=$1; shift
W=../work
for r in "$@"; do
  name=$(basename $r)
  list=$(mktemp /tmp/rbt-list.XXXX)
  GIT_CONFIG_GLOBAL=/dev/null git -C $r ls-tree -r --name-only HEAD | awk '{print NR-1"\t"$0}' > $list
  for mode in C C100 CC CCC CCC100 M M10 C10 wC; do
    case $mode in
      C) o="-C";; C100) o="-C100";; CC) o="-C -C";; CCC) o="-C -C -C";;
      CCC100) o="-C -C -C100";; M) o="-M";; M10) o="-M10";; C10) o="-C10";; wC) o="-w -C";;
    esac
    t=$(mktemp -d /tmp/rbt.XXXX)
    RB_TRACE_FILE=$t/n.trace nice -n 19 $W/rbdrive-trace $o -n -o $t $r HEAD $list 2>/dev/null
    RB_TRACE_FILE=$t/c.trace nice -n 19 $W/rbdrive-trace $o -o $t $r HEAD $list 2>/dev/null
    touch $t/n.trace $t/c.trace
    nice -n 19 ../lean/.lake/build/bin/replay $t/n.trace $t/c.trace | sed "s|^|$name\t$mode\t|" >> $out
    rm -f $t/*.txt $t/*.trace $t/stats.tsv; rmdir $t
  done
  rm -f $list
done
