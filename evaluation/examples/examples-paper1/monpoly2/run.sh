#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of NOT (P0(x1,x2) AND (NOT (P1(x1) SINCE[0,*] P0(x2,x1))))"
echo "================================================================================"
monpoly -sig ./ex.sig -formula ./ex.mfotl -log ./ex.log -no_rw -nonewlastts

echo "================================================================================"
echo "Verimon's violations of NOT (P0(x1,x2) AND (NOT (P1(x1) SINCE[0,*] P0(x2,x1))))"
echo "================================================================================"
verimon -sig ./ex.sig -formula ./ex.mfotl -log ./ex.log -no_rw -nonewlastts 


