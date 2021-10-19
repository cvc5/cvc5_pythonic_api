#!/usr/bin/env zsh

set -xe

root_dir=$(git rev-parse --show-toplevel)
cd $root_dir

python z3test.py

for ex in $(ls "test/pgms")
do
    tee_path=$(mktemp)
    script_path="test/pgms/$ex"
    output_path="test/pgm_outputs/$ex.out"
    python $script_path|tee $tee_path
    diff $output_path $tee_path || (echo "Output mismatch. \nExpected: $output_path\n Actual: $tee_path" && exit 1)
    rm $tee_path
done


