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
Usage: ./extract-ts.sh <TIMESTAMP_PATH>
Example: cat json.log | ./extract-ts.sh ".path.to.timestamp" | monpoly

Formats the content of a JSON log file to be passed to Monpoly.

The content of the log file must be passed via STDIN to this script,
while the formatted output is written to STDOUT.
Each input line must consist of a single JSON record string.

This script accepts a JSON-path pointing to the field containing the timestamp to extract.
This path is passed directly to jq and follows the same syntactic rules:
https://stedolan.github.io/jq/manual/#Basicfilters

Concrete example:
printf '{"ts": 3, "data": {}}\n{"ts": 4, "data": {}}' | ./extract-ts.sh ".ts"
results in:
@3 {"ts": 3, "data": {}}
@4 {"ts": 4, "data": {}}

EOM

if [ $# != 1 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    if [ $# != 1 ]; then
        printf "Invalid number of arguments (expected 1, but %i provided)\n\n" "$#"
    fi
    echo "$HELP_TEXT"
    exit 1
fi

json_path="$1"
while read line; do
    ts=$(printf '%s\n' "$line" | jq "$json_path")
    printf '@%s %s\n' "$ts" "$line"
done
