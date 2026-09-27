#!/bin/bash
# lane 2: make 30 wide repositories, test them end to end, then trace
# them and the random repositories 101-200.
cd "$(dirname "$0")"
for s in $(seq 5001 5030); do
  r=repos/w$s
  [ -d $r ] || nice -n 19 python3 gen_repo.py $r $s wide
  nice -n 19 python3 run_diff.py out $r
done > results-wide.tsv 2> errors-wide.log
./trace_batch.sh trace-lane2.tsv $(for s in $(seq 5001 5030); do printf 'repos/w%d ' $s; done) $(for s in $(seq 101 200); do printf 'repos/r%04d ' $s; done)
