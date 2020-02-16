#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of ((NOT (0 = 1)) UNTIL[0,1]  (EVENTUALLY [0,1] Q(x)))"
echo "================================================================================"
monpoly -sig bug.sig -formula bug1.mfotl -log bug.log  -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of ((NOT (0 = 1)) UNTIL[0,1]  (EVENTUALLY [0,1] Q(x)))"
echo "================================================================================"
verimon -sig bug.sig -formula bug1.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "MonPoly's violations of (EVENTUALLY[0,1]  (EVENTUALLY [0,1] Q(x)))"
echo "================================================================================"
monpoly -sig bug.sig -formula bug2.mfotl -log bug.log  -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of (EVENTUALLY[0,1]  (EVENTUALLY [0,1] Q(x)))"
echo "================================================================================"
verimon -sig bug.sig -formula bug2.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 



