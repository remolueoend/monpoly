#!/usr/bin/env bash

WORK_DIR=`cd "$(dirname "$BASH_SOURCE")"; pwd`
source "$WORK_DIR/functions.sh"
exec java -jar "$TOOL_JAR" "$@"
