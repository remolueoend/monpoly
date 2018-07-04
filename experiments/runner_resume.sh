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

./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-save.log $NEGATE > $SOLS/save.sol
mv checkpoint $STATES/checkpoint
./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-resume.log $NEGATE -load $STATES/checkpoint >$SOLS/resume.sol

awk 'NR>2' $SOLS/save.sol  > $SOLS/combined.sol
awk 'NR>3' $SOLS/resume.sol  >> $SOLS/combined.sol

echo "### Evaluating Results..."

python experiments/dif_checker.py -f1 $SOLS/reference.sol -f2 $SOLS/combined.sol