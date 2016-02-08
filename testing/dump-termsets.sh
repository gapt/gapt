#!/usr/bin/env bash
# Usage: dump-termsets.sh gapt-testing.jar path/to/TSTP/Solutions path/to/output/termsets/

set -e

gapt_testing_jar=`readlink -f $1`
tstp_solutions_dir=`readlink -f $2`
output_dir=$3

mkdir -p $output_dir
cd $output_dir

echo -n >input_proofs

for seq_name in \
  LinearExampleProof \
  LinearEqExampleProof \
  SquareDiagonalExampleProof \
  SquareEdgesExampleProof \
  SquareEdges2DimExampleProof \
  SumExampleProof \
  SumOfOnesF2ExampleProof \
  SumOfOnesFExampleProof \
  SumOfOnesExampleProof \
  UniformAssociativity3ExampleProof \
  FactorialFunctionEqualityExampleProof \
  FactorialFunctionEqualityExampleProof2 \

do
  for i in {0..100}; do
    echo "$seq_name($i)" "proofseq-${seq_name}-${i}.termset" >>input_proofs
  done
done

find $tstp_solutions_dir -not -type d -name \*.s | \
  perl -ne 'chop;m,/([^/]+)/([^/]+)\.[^./]+\.s$,;print"$_ tstp-$1-$2.termset\n"' \
  >>input_proofs

shuf -o input_proofs input_proofs

parallel --timeout 60 \
  --colsep ' ' \
  --joblog joblog --resume \
  --progress --eta --bar \
  --group \
  java -cp $gapt_testing_jar \
  -Xmx1G -Xss40m \
  -XX:ParallelGCThreads=1 -XX:ConcGCThreads=1 \
  at.logic.gapt.testing.dumpTermset '{1}' '{2}' \
  :::: input_proofs 2>&1 | tee -a stdout || true
