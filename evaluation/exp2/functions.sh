[[ -n $WORK_DIR ]] || WORK_DIR=`cd "$(dirname "$BASH_SOURCE")"; pwd`
[[ -n $EVAL_DIR ]] || EVAL_DIR=`cd "$WORK_DIR/.."; pwd`


TOOL_JAR="$EVAL_DIR/evaluation-tools-1.0-SNAPSHOT.jar"
DEJAVU_COMPILE="$EVAL_DIR/dejavu-compile"
DEJAVU_RUN="$EVAL_DIR/dejavu-run"
OUTPUT_DIR="$WORK_DIR/logs"
VERDICT_DIR="$WORK_DIR/verdicts"
REPORT_DIR="$WORK_DIR/reports"

EXP_NAME="sltrandom"
WINDOW=10


# ============================================================
# OUTPUT functions
# ============================================================

SILENT=false
DEBUG=false

function debug() {
    if [[ ${DEBUG} == "true" ]]; then
        echo "[DEBUG]" "$@" 1>&2
    fi
}

function info() {
    if [[ ${SILENT} != "true" ]]; then
        echo "[INFO]" "$@" 1>&2
    fi
}

function error() {
    if [[ ${SILENT} != "true" ]]; then
        echo "[ERROR]" "$@" 1>&2
    fi
    exit 0
}

# ============================================================
# Log generation functions
# ============================================================


function log_path() {
    local log=$1
    echo "$OUTPUT_DIR/${log}"
}

function log_name() {
    local adaptations=$1
    local formula=$2
    local er=$3
    local ir=$4
    local part=$5
    local seed=$6
    local numcpus=$7

    local name="${EXP_NAME}_${adaptations}_${formula}_${er}_${ir}_part${part}"

    if [ -z "$seed" ]; then 
        echo $name
    else
        echo "${name}_seed${seed}"
    fi
}


function make_log() {
    local formula=$1
    local er=$2
    local ir=$3
    local part=$4
    local adaptations=$5
    local length=$6
    local strategy=$7

    local start=$((length*part))
    local seed=$RANDOM

    local name=$(log_name "$adaptations" "$formula" "$er" "$ir" "$length" "$seed")
    local log=$(log_path $name)

    if [ -f "$log" ]; then
        debug "           Log exists, skipping..."
    else
        "gen_log" -policy $formula -event_rate $er -first_ts 30 -seed_index $seed -time_span $length > $log 
        cat ${log} | cut -d " " -f2,3 | sed "s/ (/,/g" | sed "s/)//g" > ${log}_dejavu  
    fi
    echo "${name}"
}

# ============================================================
# Monitoring functions
# ============================================================

TIME="\time -f %M"

function verdict_path() {
    local v=$1
    echo "$VERDICT_DIR/${v}"
}


# runs all tools on a log and writes verdicts into a file and returns running time and space
function run() {
    local cmd=$1
    
    local ts1=$(date +%s%N)

    debug "Start monitoring"

    local result=$( { eval "$TIME $cmd"; } 2>&1 )

    debug "Finished monitoring"

    local ts2=$(date +%s%N)
    local delta=$((ts2 - ts1))
    local time=`bc <<< "scale=2; $delta/1000000000"`
    
    #returns time
    echo "$time, $result"
}


function  compare() {
    local tool=$1
    local toolCMD=$2
    local oracleCMD=$3
    local log=$4

    local verdictpath=$(verdict_path $log)

    #TOOL
    local perf=$(run "$toolCMD")
    echo ${perf} > ${REPORT_DIR}/${log}_perf_${tool}

    #ORACLE
    local perf=$(run "$oracleCMD")
    echo ${perf} > ${REPORT_DIR}/${log}_perf_oracle_${tool}

    #DIFF
    diff ${verdictpath}_oracle_${tool} ${verdictpath}_${tool} > ${REPORT_DIR}/${log}_diff_${tool}
    
    if [ $? -eq 0 ]; then
        #no difference
        rm ${REPORT_DIR}/${log}_diff_${tool}
    fi

}

function monitor() {
    local fma=$1
    local log=$2

    local formula=""
    local formula_oracle_dejavu=""
    local formula_dejavu=""
    case ${fma} in 
        P1) 
            formula="P1.mfotl -negate"
            formula_oracle_dejavu="P1-past-ltl.mfotl -negate"
            formula_dejavu="P1-past-ltl"
        ;;
        P2) 
            formula="P2.mfotl"
            formula_oracle_dejavu="P2-past-ltl.mfotl"
            formula_dejavu="P2-past-ltl"
        ;;
        P3) 
            formula="P3.mfotl"
            formula_oracle_dejavu="P3-past-ltl.mfotl"
            formula_dejavu="P3-past-ltl"
        ;;
        P4) 
            formula="P4.mfotl  -negate"
            formula_oracle_dejavu="P4-past-ltl.mfotl  -negate"
            formula_dejavu="P4-past-ltl"
        ;;
        *) 
            error "Formula ${fma} does not exist"
        ;;
    esac
    local logpath=$(log_path $log)
    local verdictpath=$(verdict_path $log)

    #MONPOLY
    local monpolyCMD="monpoly -no_rw -nonewlastts -sig ${WORK_DIR}/synth.sig -formula ${WORK_DIR}/${formula} -log ${logpath} > ${verdictpath}_monpoly"
    
    #ORACLE-Monpoly
    local oracleCMD="verimon -no_rw -nonewlastts -sig ${WORK_DIR}/synth.sig -formula ${WORK_DIR}/${formula} -log ${logpath} -verified > ${verdictpath}_oracle_monpoly"
    
    compare "monpoly" "${monpolyCMD}" "${oracleCMD}" "${log}"

    #DEJAVU
    local dejavuCMD="${DEJAVU_RUN} ${WORK_DIR}/${formula_dejavu} ${logpath}_dejavu ${verdictpath}_dejavu"

    #ORACLE-Dejavu
    local oracleCMD="verimon -no_rw -nonewlastts -sig ${WORK_DIR}/synth.sig -formula ${WORK_DIR}/${formula_oracle_dejavu} -log ${logpath} -verified | cut -d ' ' -f4 | cut -d ')' -f1 | xargs -I J sh -c \"echo 'J+1' | bc -l\" > ${verdictpath}_oracle_dejavu"

    compare "dejavu" "${dejavuCMD}" "${oracleCMD}" "${log}"
}

