#!/bin/bash


#Policy to be evaluated (P1/P2/P3)
P=$1
#Type of test (resume/combine)
T=$2
#Duplicates in combine file (true/false)
D=$3

if [ -z ${3+x} ]; then D="false"; fi

if [ -z $P ] || [ -z $T ]; then
    echo "Usage of this script:"
    echo " - \$1: Policy to be run (P1/P2/P3)"
    echo " - \$2: Type of test     (resume/combine)"
    echo " - \$3 (optional): Duplicate entries (true/false), only relevant for combine test"
    echo " - Usage Example: 'examples/experiments/experiment_runner.sh P2 combine true'"
    exit 1
fi

if [ $P != "P1" ] && [ $P != "P2" ] && [ $P != "P3" ]; then
    echo " - \$1: Policy must be one of [\"P1\", \"P2\", \"P3\"]"
    exit 1
fi

if [ $T != "resume" ] && [ $T != "combine" ]; then
    echo " - \$2: Test must be one of [\"resume\", \"combine\"]"
    exit 1
fi


#Directories
EX=examples
EXP=$EX/experiments
SCRIPTS=$EX/scripts
LOGS=$EX/logs/$P
SIGS=$EX/sigs
MFOTL=$EX/mfotl

#Create necessary directory structure
mkdir -p $LOGS

#Generate log files
(cd $SCRIPTS; ocamlopt -o gen_log PrioQueue.ml gen_log.ml)
$SCRIPTS/gen_log -policy $P > $LOGS/$P.log
python $SCRIPTS/split_log.py -p $P -i $LOGS/$P.log -o $LOGS/$P -d $D


#Run appropriate experiment

if [ "$P" == "P1" ]; then
    NEGATE="-negate"
fi

echo "### Cleaning"...""
make clean-all > /dev/null
echo "### Building..."
make monpoly   > /dev/null

STATES=$EXP/tmp/states/$P
OUTPUT=$EXP/tmp/output/$P

rm -r $STATES
rm -r $OUTPUT
mkdir -p $STATES
mkdir -p $OUTPUT

echo "### Running Experiment..."


if [ $T == "combine" ]; then
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P.log $NEGATE > $OUTPUT/tmp.log
    awk 'NR>2' $OUTPUT/tmp.log > $OUTPUT/reference.log && rm $OUTPUT/tmp.log

    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-start.log $NEGATE > $OUTPUT/start.log
    mv partition-0 $STATES/left-ss
    mv partition-1 $STATES/right-ss
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-left.log  -load $STATES/left-ss $NEGATE > $OUTPUT/left.log
    mv left-es  $STATES/left-es
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-right.log -load $STATES/right-ss $NEGATE > $OUTPUT/right.log
    mv right-es $STATES/right-es
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-end.log -combine $STATES/left-es,$STATES/right-es $NEGATE > $OUTPUT/end.log

    awk 'NR>2' $OUTPUT/start.log  > $OUTPUT/combined.log
    awk 'NR>3' $OUTPUT/left.log  >> $OUTPUT/combined.log
    awk 'NR>3' $OUTPUT/right.log >> $OUTPUT/combined.log
    awk 'NR>2' $OUTPUT/end.log   >> $OUTPUT/combined.log
elif [ $T == "resume" ]; then
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P.log $NEGATE > $OUTPUT/tmp.log
    awk 'NR>2' $OUTPUT/tmp.log > $OUTPUT/reference.log && rm $OUTPUT/tmp.log

    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-save.log $NEGATE > $OUTPUT/save.log
    mv checkpoint $STATES/checkpoint
    ./monpoly -sig $SIGS/$P.sig -formula $MFOTL/$P.mfotl -log $LOGS/$P-resume.log $NEGATE -load $STATES/checkpoint >$OUTPUT/resume.log

    awk 'NR>2' $OUTPUT/save.log  > $OUTPUT/combined.log
    awk 'NR>3' $OUTPUT/resume.log  >> $OUTPUT/combined.log
fi


echo "### Evaluating Results..."

python $EXP/dif_checker.py -f1 $OUTPUT/reference.log -f2 $OUTPUT/combined.log