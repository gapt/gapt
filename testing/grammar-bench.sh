#!/usr/bin/env bash
# Usage: grammar-bench.sh gapt-testing.jar termsets...

set -e

gapt_testing_jar=`readlink -f $1`
shift

methods='
1_dtable
1_dtable_new
many_dtable
many_dtable_new
many_dtable_ss_new
1_maxsat
2_maxsat
3_maxsat
'

parallel --timeout 60 \
  --colsep ' ' \
  --joblog grammar-bench-joblog \
  --progress --eta --bar \
  "java -cp $gapt_testing_jar \
  -Xmx1G -Xss40m \
  -XX:ParallelGCThreads=1 -XX:ConcGCThreads=1 \
  gapt.testing.loadAndCompress {1} {2} 2>&1" \
  ::: $methods ::: $@ || true
