#!/bin/bash

echo "================================================================================"
echo "MonPoly's violations of (Q() SINCE[0,0)  P())"
echo "================================================================================"
monpoly -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 

echo "================================================================================"
echo "Verimon's violations of (Q() SINCE[0,0)  P())"
echo "================================================================================"
verimon -sig bug.sig -formula bug.mfotl -log bug.log -no_rw -nonewlastts -nofilteremptytp -nofilterrel 
