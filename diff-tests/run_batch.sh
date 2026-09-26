#!/bin/bash
# run_batch.sh <first-seed> <last-seed> <lane>: make and test repositories
cd "$(dirname "$0")"
for s in $(seq $1 $2); do
  r=repos/r$(printf %04d $s)
  [ -d $r ] || nice -n 19 python3 gen_repo.py $r $s
  nice -n 19 python3 run_diff.py out $r
done > results-lane$3.tsv 2> errors-lane$3.log
