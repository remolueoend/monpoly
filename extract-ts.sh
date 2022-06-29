#!/usr/bin/sh

# Author: zumstegr@student.ethz.ch
#
# Description:
# Formats the content of a JSON log file to be passed to Monpoly.
# Run this script without arguments for more information
#
# Dependencies:
# jq : JSON parser

# exit on error, undefined var, pipefail
set -euo pipefail

read -r -d '' HELP_TEXT <<-EOM || :
Usage: cat json.log | ./extract-ts.sh ".path.to.timestamp" | monpoly

Formats the content of a JSON log file to be passed to Monpoly.

The content of the log file must be passed via STDIN to this script.
This script writes the formatted lines to STDOUT.

Each line is expected to consist of a single JSON record string.
This script accepts a JSON-path pointing to the field containing the timestamp to extract. This path is passed directly to jq.
EOM

if [ $# != 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    if [ $# != 1 ]; then
        printf "Invalid number of arguments\n\n"
    fi
    echo "$HELP_TEXT"
    exit 1
fi

json_path="$1"
while read line; do
    ts=$(printf '%s\n' "$line" | jq "$json_path")
    printf '@%s %s\n' "$ts" "$line"
done
