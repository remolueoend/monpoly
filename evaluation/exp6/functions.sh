[[ -n $WORK_DIR ]] || WORK_DIR=`cd "$(dirname "$BASH_SOURCE")"; pwd`
[[ -n $EVAL_DIR ]] || EVAL_DIR=`cd "$WORK_DIR/.."; pwd`


TOOL_JAR="$EVAL_DIR/evaluation-tools-1.0-SNAPSHOT.jar"
OUTPUT_DIR="$WORK_DIR/logs"
FMA_DIR="$WORK_DIR/fmas"
VERDICT_DIR="$WORK_DIR/verdicts"
REPORT_DIR="$WORK_DIR/reports"

EXP_NAME="mdlcompliance"


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


function fma_path() {
    local fma=$1
    echo "$FMA_DIR/${fma}"
}


function fma_name() {
    local size=$1
    local fvs=$2
    local id=$3

    echo "-F-${size}-${fvs}-${id}"
}

function make_fma {
    local size=$1
    local fvs=$2
    local id=$3

    local name=$(fma_name "$size" "$fvs" "$id")
    local fma=$(fma_path $name)

    echo "P()"  > "${fma}.sig"
    echo "Q()" >> "${fma}.sig"
    echo "R()" >> "${fma}.sig"
    gen_mdl_fma -size $size -atoms P,Q,R > "${fma}.mdl"
    echo "${name}"
}

function make_log() {
    local formula=$1
    local er=$2
    local ir=$3
    local part=$4
    local adaptations=$5
    local length=$6
    local strategy=$7

    local seed=$RANDOM

    local name=$(log_name "$adaptations" "$formula" "$er" "$ir" "$length" "$seed")
    local log=$(log_path $name)
    local fma=$(fma_path $formula)

    if [ -f "$log" ]; then
        debug "           Log exists, skipping..."
    else
        "$WORK_DIR/generator.sh" -seed $seed -e $er -i $ir -t 0 -sig ${fma}.sig $length > ${log}_tmp$$
        cat ${log}_tmp$$ | "$WORK_DIR/replayer.sh" -a 0 -m > ${log} 
        rm ${log}_tmp$$

    fi
    echo "${name}"
}

# ============================================================
# Monitoring functions
# ============================================================

TIME="\time -f %M"
TIMEOUTCMD="timeout --foreground"
TIMEOUT=60

function verdict_path() {
    local v=$1
    echo "$VERDICT_DIR/${v}"
}

function diff_prefix {
    local f1=$1
    local f2=$2
    local result=$3

    local l1=$(cat $f1 | wc -l)
    local l2=$(cat $f2 | wc -l)

    local min=$l1
    if [ $min -gt $l2 ]; then
        min=$l2
    fi
    head -$min "${f1}" > "${f1}_tmp"
    head -$min "${f2}" > "${f2}_tmp"

    diff ${f1}_tmp ${f2}_tmp > $result
    local res=$?

    rm ${f1}_tmp
    rm ${f2}_tmp

    return $res
}


# runs all tools on a log and writes verdicts into a file and returns running time and space
function run() {
    local cmd=$1
    
    local ts1=$(date +%s%N)

    debug "Start monitoring"

    eval "$TIMEOUTCMD $TIMEOUT $TIME -o time.log $cmd"
    status=$(echo $?)
    local result=$( cat time.log )
    rm -f time.log

    space=$(echo "$result" | grep -oE '[^ ]+$' | tail -1)

    if [ "$status" == "2" ]; then
        echo "$cmd" >> /tmp/error.log
        echo "REASON: $result" >> /tmp/error.log
    else 
        if [ "$space" != "$result" ]; then
            echo "$cmd" >> /tmp/error.log
            echo "REASON: $result" >> /tmp/error.log
        fi
    fi

    if [ "$status" == "124" ]; then
        echo "$cmd" >> /tmp/error.log
        echo "REASON: timeout" >> /tmp/error.log
    fi

    debug "Finished monitoring"

    local ts2=$(date +%s%N)
    local delta=$((ts2 - ts1))
    local time=`bc <<< "scale=2; $delta/1000000000"`
    
    #returns time
    if [ $status == "0" ]; then
        echo "$time, $space"
    else
        echo ""
    fi
}


function  compare() {
    local tool=$1
    local toolCMD=$2
    local oracleCMD=$3
    local log=$4

    local verdictpath=$(verdict_path $log)

    #TOOL
    local perf1=$(run "$toolCMD")
    
    #ORACLE
    local perf2=$(run "$oracleCMD")
    

    if [ "$perf1" != "" ] && [ "$perf2" != "" ]; then 

        echo ${perf1} > ${REPORT_DIR}/${log}_perf_${tool}
        echo ${perf2} > ${REPORT_DIR}/${log}_perf_oracle_${tool}
        #DIFF
        diff ${verdictpath}_oracle ${verdictpath}_${tool} > ${REPORT_DIR}/${log}_diff_${tool}
        
        if [ $? -eq 0 ]; then
            #no difference
            rm ${REPORT_DIR}/${log}_diff_${tool}
        else 
            diff_prefix ${verdictpath}_oracle ${verdictpath}_${tool} ${REPORT_DIR}/${log}_diff_${tool}
            if [ $? -eq 0 ]; then
                #no difference
                rm ${REPORT_DIR}/${log}_diff_${tool}
            fi
        fi
    fi

}

function monitor() {
    local formula=$1
    local log=$2
    local er=$3

    
    local logpath=$(log_path $log)
    local verdictpath=$(verdict_path $log)
    local fma=$(fma_path $formula)

    #MONPOLY
    local aerialCMD="aerial -fmla ${fma}.mdl -log ${logpath} -mode naive | sed  '/^[A-Z]/d' | grep false | sort -n > ${verdictpath}_aerial"
    
    #ORACLE-Monpoly
    local oracleCMD="verimon -no_rw -nofilteremptytp -nofilterrel -sig ${fma}.sig -formula ${fma}.mdl -log ${logpath} -negate -verified | sed 's/@//g;s/. (time point /:/g;s/)://g;s/ true/:false/g' | awk -F':' -v d=${er} '{print \$1,(\$2 % d),\$3}' OFS=':' | sed 's/:false/ false/g' > ${verdictpath}_oracle"

    compare "aerial" "${aerialCMD}" "${oracleCMD}" "${log}"

    #Hydra
    local hydraCMD="hydra ${fma}.mdl ${logpath} | sed  '/^[A-Z]/d' > ${verdictpath}_hydra"

    compare "hydra" "${hydraCMD}" "${oracleCMD}" "${log}"
}

