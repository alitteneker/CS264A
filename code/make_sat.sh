#!/bin/bash

cd primitives
make clean
make
cd ../sat_solver
make clean
make
cd ..
