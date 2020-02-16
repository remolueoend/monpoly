#!/usr/bin/env bash

# Experiments that run MonPoly without Flink

# PREAMBLE & PRIVATE PARAMETERS
WORK_DIR=`cd "$(dirname "$BASH_SOURCE")"; pwd`
EVAL_DIR=`cd "$WORK_DIR/.."; pwd`
source "$WORK_DIR/functions.sh"




# EXPERIMENT PARAMETERS:
REPETITIONS=1
FORMULAS="multiway/monpoly;verimon;verimon-old sliding/monpoly;verimon;verimon-old aggregation/monpoly;verimon regex/aerial;hydra;verimon"
EVENT_RATES="10 50 100 200 500 1000 2000 4000" 
LOG_LENGTH="60"

function monitor_cmd() {
  local monitor=$1
  local fma=$2
  local log=$3

  if [ $monitor = "monpoly" ]; then
      echo "monpoly -nofilteremptytp -nofilterrel -no_rw -nonewlastts -sig ${fma}.sig -formula ${fma}.mfotl -log ${log} > /dev/null"
      return
  fi

  if [ $monitor = "dejavu" ]; then
      echo "${DEJAVU_RUN} ${fma} ${log}_dejavu verdict.txt; rm verdict.txt"
      return
  fi

  if [ $monitor = "verimon" ]; then
      echo "verimon -no_rw -nofilteremptytp -nofilterrel -nonewlastts -sig ${fma}.sig -formula ${fma}.mfotl -log ${log} -verified > /dev/null"
      return
  fi

  if [ $monitor = "verimon-old" ]; then
      echo "verimon-old -no_rw -nofilteremptytp -nofilterrel -nonewlastts -sig ${fma}.sig -formula ${fma}.mfotl -log ${log} -verified > /dev/null"
      return
  fi

  if [ $monitor = "hydra" ]; then
      echo "hydra ${fma}.mdl ${log} > /dev/null"
      return
  fi

  if [ $monitor = "aerial" ]; then
      echo "aerial -fmla ${fma}.mdl -log ${log} -mode global -expr  -out /dev/null"
      return
  fi

   #... 
}


TIFS=$IFS
for f in $FORMULAS; do
  fma=$(echo $f | cut -d "/" -f 1)
  monitors=$(echo $f | cut -d "/" -f 2)
  fma_file=$(fma_path ${fma})
  info "  Formula ${fma} (out of $FORMULAS)"

    for e in $EVENT_RATES; do
        info "     Event rate: ${e} (out of $EVENT_RATES)"

        for r in $(seq 1 $REPETITIONS); do
        info "      Repetition ${r} (out of $REPETITIONS)"

        info "       Generating log ..."

        if [ $fma = "regex" ]; then
            name=$(make_log "$fma" "$e" "$e" "1" "$r" "$LOG_LENGTH" "-sig ./fmas/regex.sig")
        else
            if [ $fma = "multiway" ]; then
                name=$(make_log "$fma" "$e" "1" "1" "$r" "$LOG_LENGTH" "-S -z w=1")
            else
                name=$(make_log "$fma" "$e" "1" "1" "$r" "$LOG_LENGTH" "-S")
            fi
        fi

        export IFS=";"
        for m in $monitors; do
            export IFS=$TIFS
            info "    Monitor: ${m} (out of $monitors)"

            info "       Monitoring ..."
            log=$(log_path $name)
            cmd=$(monitor_cmd "$m" "$fma_file" "$log")
            # echo "$cmd"
            if [ $m = "dejavu" ]; then
                run "$cmd" > /dev/null # to avoid measuring compiling time with Dejavu
            fi
            perf=$(run "$cmd")
            echo ${perf} > ${REPORT_DIR}/${name}_perf_${m}

      done
    done
  done
done
    


