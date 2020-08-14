#!/bin/bash

echo "================================================================================"
echo "Hydra's violations of ▷ [1,3] ( . . . . ( P() OR (▷ [2,3] . ) )? )"
echo "================================================================================"
hydra bug.mdl bug.log | sed  '/^[A-Z]/d'

echo "================================================================================"
echo "Verimon's violations of ▷ [1,3] ( . . . . ( P() OR (▷ [2,3] . ) )? )"
echo "================================================================================"
verimon -sig bug.sig -formula bug.mdl -log bug.log -no_rw -nofilteremptytp -nofilterrel -negate | sed 's/@//g;s/. (time point /:/g;s/)://g;s/ true/:false/g' | awk -F':' -v d=5 '{print $1,($2 % d),$3}' OFS=':' | sed 's/:false/ false/g' 
