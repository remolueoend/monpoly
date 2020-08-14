#!/bin/bash

echo "======================================================================="
echo "DejaVu's violations of ! (Exists x1. (x1=24 & !P3(x1))) "
echo "======================================================================="
./dejavu ./ex.qtl ./ex.csv > /dev/null 2> /dev/null
cat dejavu-results

echo "======================================================================="
echo "Verimon's violations of ! (Exists x1. (x1=24 & !P3(x1)))"
echo "======================================================================="
verimon -sig ./ex.sig -formula ./ex.mfotl -log ./ex.log -no_rw -nonewlastts | cut -d ' ' -f4 | cut -d ')' -f1 | xargs -I J sh -c "echo 'J+1' | bc -l"


