#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of NOT (NOT P0() AND (ONCE[0,*] P1(x1)))"
echo "================================================================================"
monpoly -sig ex.sig -formula ex.mfotl -log ex.log  -no_rw

echo "================================================================================"
echo "Verimon's violations of NOT (NOT P0() AND (ONCE[0,*] P1(x1)))"
echo "================================================================================"
verimon -sig ./ex.sig -formula ./ex.mfotl -log ./ex.log -no_rw -nonewlastts


