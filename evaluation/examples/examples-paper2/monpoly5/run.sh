#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of  (x1 <- MAX x1; x2 (ONCE[1,1] (P0(y1,x1,x2) )))"
echo "================================================================================"
monpoly -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of  (x1 <- MAX x1; x2 (ONCE[1,1] (P0(y1,x1,x2) )))"
echo "================================================================================"
verimon -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 
