#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of (NOT EVENTUALLY[0,2] P()) UNTIL[0,1] Q()"
echo "================================================================================"
monpoly -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of (NOT EVENTUALLY[0,2] P()) UNTIL[0,1] Q()"
echo "================================================================================"
verimon -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 
