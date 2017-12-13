#!/bin/bash
./abc -c "r PA2_testcase/c17.blif" -c "1subfind" & 
./abc -c "r PA2_testcase/c432.blif" -c "1subfind" &
./abc -c "r PA2_testcase/c499.blif" -c "1subfind" &
./abc -c "r PA2_testcase/c880.blif" -c "1subfind" &
./abc -c "r PA2_testcase/c1355.blif" -c "1subfind" 

