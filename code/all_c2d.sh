#!/bin/bash

FILES=benchmarks/sampled/*.cnf
for f in $FILES
do

  echo "Testing $f . . ."
  ./c2D_code/bin/darwin/c2D -c $f -C -E

done
