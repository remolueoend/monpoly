#!/bin/bash
P=$1

if [ "$P" == "P1" ]; then 
    NEGATE="-negate"
fi

echo "### Cleaning"...""
make clean-all > /dev/null
echo "### Building..."
make monpoly   > /dev/null

STATES=experiments/states/$P
LOGS=examples/logs/$P
SIGS=examples/sigs
MFOTL=examples/mfotl
SOLS=experiments/solutions/$P

rm -r $STATES
rm -r $SOLS
mkdir -p $STATES
mkdir -p $SOLS

echo "### Running Experiment..."

./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P.log $NEGATE > $SOLS/tmp.sol
awk 'NR>2' $SOLS/tmp.sol > $SOLS/reference.sol && rm $SOLS/tmp.sol

./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-start.log $NEGATE > $SOLS/start.sol
mv partition-0 $STATES/left-ss
mv partition-1 $STATES/right-ss
./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-left.log  -load $STATES/left-ss $NEGATE > $SOLS/left.sol
mv left-es  $STATES/left-es
./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-right.log -load $STATES/right-ss $NEGATE > $SOLS/right.sol
mv right-es $STATES/right-es
./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-end.log -combine $STATES/left-es,$STATES/right-es $NEGATE > $SOLS/end.sol

awk 'NR>2' $SOLS/start.sol  > $SOLS/combined.sol
awk 'NR>3' $SOLS/left.sol  >> $SOLS/combined.sol
awk 'NR>3' $SOLS/right.sol >> $SOLS/combined.sol
awk 'NR>2' $SOLS/end.sol   >> $SOLS/combined.sol

echo "### Evaluating Results..."

python experiments/dif_checker.py -f1 $SOLS/reference.sol -f2 $SOLS/combined.sol