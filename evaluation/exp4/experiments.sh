#!/usr/bin/env bash

# Experiments that run MonPoly without Flink

# PREAMBLE & PRIVATE PARAMETERS
WORK_DIR=`cd "$(dirname "$BASH_SOURCE")"; pwd`
EVAL_DIR=`cd "$WORK_DIR/.."; pwd`
source "$WORK_DIR/functions.sh"


# EXPERIMENT PARAMETERS:
REPETITIONS=100
FORMULAS="2;1 3;1 3;3 3;6 4;2 4;4 4;9 5;2 10;5" #5;3 5;5 5;8 6;1 6;4 10;3 10;5 15;3 15;5 15;10 20;2 20;5 20;10 50;5 50;10 100;10 100;20"
EVENT_RATES="5" 
INDEX_RATES="5"
LOG_LENGTH="5 10 20 40 60"
NUM_ADAPTATIONS='0/1/ '

# Log generation strategies 
# Equal relation ratios and uniform value distribution (i.e., -pA 0.3333 -pB 0.3333 -z x=0,y=0,z=0,w=0)
# Params                                                                                                        |  Explanation
# num_adapt/ID/strategies                                                                                       |
# -----------------------------------------------------------------------------------------------------------------------------------------------------
#2/1/-x 0.01;-x 0.01;-pA 0.01 -pB 0.495 -x 0.01                                                                 |  change relation rates (less A)
#2/2/-x 0.01;-x 0.01;-pA 0.495 -pB 0.495 -x 0.005                                                               |  change relation rates (less C)
#2/3/-x 0.01;-x 0.01;-pA 0.01 -pB 0.01 -x 0.01                                                                  |  change relation rates (less A and B)
#2/4/-x 0.01;-x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01                                                           |  introduce a single HH value
#2/5/-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01;-x 0.01                                  |  remove a single HH value
#2/6/-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+2000,y=0,z=0,w=0 -x 0.01         |  change a single HH value
#2/7/-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=2+1000,y=0,z=0,w=0 -x 0.01          |  change the number of HH values
#2/8/-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=0,y=10+1000,z=0,w=0 -x 0.01         |  change the HH variable
#2/9/-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=0,z=0,w=0 -x 0.01;-z x=10+1000,y=10+2000,z=0,w=0 -x 0.01   |  change the number of HH variables




# ============================================================
# Script parameters 
# ============================================================

EXP_NAME="random"


function parse_options() {
    local option
    while [[ $# -gt 0 ]]; do
        option="$1"
        shift
        case ${option} in
            -h|-H|--help)
                usage
                exit 0
                ;;
            -v|-V|--verbose)
                DEBUG=true
                ;;
            -s|-S|--silent)
                SILENT=true
                ;;
            -n|-N|--name)
                if [ ! -z "$1" ]; then 
                    EXP_NAME=$1 
                else
                    echo "Invalid argument was provided: ${option}"
                    usage
                    exit 1
                fi
                shift
                ;;
            -c|-C|--config)
                if [ -e "$1" ]; then 
                    source $1 
                else 
                    echo "Invalid argument was provided: ${option}"
                    usage 
                    exit 1
                fi
                shift
                ;;
            *)
                echo "Invalid argument was provided: ${option}"
                usage
                exit 1
                ;;
        esac
    done
}

function usage() {
    script_name="$(basename "${BASH_SOURCE[0]}")"
    
cat << EOF
Usage: ${script_name} [OPTION]...
Runs adaptive monitoring experiments with MonPoly sequentially and without Flink.
Edit the topmost uppercase variables in order to change parameters of the experiments.
Version: ${script_version}
Options:
  -h|--help           Displays this help
  -s|--silent         Displays no output
  -v|--verbose        Displays debug output
  -n|--name NAME      Sets the name of the experiment
  -c|--config FILE    Sources FILE, (presumably) overriding experiment parameters (e.g., NUM_ADAPTATIONS)
EOF
}



# ============================================================
# Script body 
# ============================================================

parse_options "$@"

#Compile the generator

info "=== Running random formula & random traces experiments ==="

# FOR each param
TIFS=$IFS
for f in $FORMULAS; do
    info "  Formula ${f} (out of $FORMULAS)"

    size=$(echo $f | cut -d ";" -f 1)
    fvs=$(echo $f | cut -d ";" -f 2)
    for r in $(seq 1 $REPETITIONS); do
        info "  Repetition ${r} (out of $REPETITIONS)"
        fma_name=$(make_fma "$size" "$fvs" "$r")
        fma=$(fma_path ${fma_name})
        for er in $EVENT_RATES; do
            info "    Event rate: ${er} (out of $EVENT_RATES)"
            for ir in $INDEX_RATES; do
                info "      Index rate: ${ir} (out of $INDEX_RATES)"
                export IFS="#"
                for ads in $NUM_ADAPTATIONS; do
                    tmp=${ads%/*}
                    adaptations=${tmp%/*}
                    num=${tmp#*/}
                    tmp=${ads#*/}
                    strategies=${tmp#*/}
                    export IFS=$TIFS
                    for length in $LOG_LENGTH; do
                        info "        Log length: ${length} (out of $LOG_LENGTH)"
                        for part in `seq 0 $adaptations`; do

                                strategy=$(echo $strategies | cut -d ";" -f $((a+1)))
                                info "            Generating log ..."
                                log=$(make_log "$fma_name" "$er" "$ir" "$part" "$r" "$length" "$strategy")
                                
                                info "            Monitoring ... "
                                monitor "${fma_name}" "${log}"
                            
                        done
                    done
                done
            done
        done
    done
done

info "Done! Following differences found:"
diffs=$(ls ${REPORT_DIR} | grep diff)
echo "$diffs"

echo "$diffs" > results.txt


