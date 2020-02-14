#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of (r <- SUM x  ONCE P(x))"
echo "================================================================================"
monpoly -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of (r <- SUM x  ONCE P(x))"
echo "================================================================================"
verimon -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 
