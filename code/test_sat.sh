#!/bin/bash

FILES=benchmarks/*/*.cnf
for f in $FILES
do
  echo "Testing $f . . ."

  printf "\tOracle: "
  START=$(date +%s)
  echo -n "$(./executables/sat/darwin/sat -c $f)"
  END=$(date +%s)
  DIFF=$(echo "$END - $START" | bc)
  printf " $DIFF \n"

  printf "\tOurs:   "
  START=$(date +%s)
  echo -n "$(./sat_solver/sat -c $f)"
  END=$(date +%s)
  DIFF=$(echo "$END - $START" | bc)
  printf " $DIFF \n"

done
