#!/bin/bash

cd primitives
make clean
make

cd ../sat_solver
make clean
make

cd ../c2D_code
make clean
make

cd ..
