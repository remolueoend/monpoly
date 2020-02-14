#!/bin/bash

echo ""
echo "For a fixed formula ((ONCE[0,10) A(a,b)) AND B(a,c)) AND EVENTUALLY[0,10) C(a,d)"
echo ""

echo "================================================================================"
echo "MonPoly's performance on a log with 40000 events"
echo "================================================================================"
\time -f "Time: %e s Memory: %M KB" monpoly -sig synth.sig -formula ./star.mfotl -log ./400.log -no_rw -nonewlastts > /dev/null

echo "================================================================================"
echo "Verimon's performance on a log with 40000 events"
echo "================================================================================"
\time -f "Time: %e s Memory: %M KB" verimon -sig synth.sig -formula ./star.mfotl -log ./400.log -no_rw -nonewlastts > /dev/null


