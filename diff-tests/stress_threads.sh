#!/bin/bash
# stress_threads.sh <repo> <opts...>: list each file 20 times, blame the
# list with 2 threads and a cache of 1 byte (and of 64 KiB), and compare
# every copy with the reference (-n).  Prints: repo copies differing.
cd "$(dirname "$0")"
r=$1; shift
W=../work
t=$(mktemp -d /tmp/rbs.XXXX)
GIT_CONFIG_GLOBAL=/dev/null git -C $r ls-tree -r --name-only HEAD > $t/files
awk '{print NR-1"\t"$0}' $t/files > $t/ref.tsv
for k in $(seq 1 20); do awk -v k=$k '{print k*1000+NR-1"\t"$0}' $t/files; done | shuf --random-source=<(yes) > $t/many.tsv
mkdir $t/ref $t/a $t/b
nice -n 19 $W/rbdrive "$@" -n -o $t/ref $r HEAD $t/ref.tsv 2>/dev/null
nice -n 19 $W/rbdrive "$@" -j 2 -b 1 -o $t/a $r HEAD $t/many.tsv 2>/dev/null
nice -n 19 $W/rbdrive "$@" -j 2 -b 65536 -r 2 -o $t/b $r HEAD $t/many.tsv 2>/dev/null
bad=0; n=0
while IFS=$'\t' read idx p; do
  i=$((idx % 1000))
  for v in a b; do
    n=$((n+1))
    cmp -s $t/ref/$i.txt $t/$v/$idx.txt || bad=$((bad+1))
  done
done < $t/many.tsv
echo -e "$(basename $r)\t$*\t$n\t$bad"
rm -f $t/ref/* $t/a/* $t/b/* $t/files $t/ref.tsv $t/many.tsv; rmdir $t/ref $t/a $t/b $t
