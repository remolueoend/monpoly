#!/bin/bash
set -e

SESSIONS="MFOTL_Monitor_Devel:MFOTL_Monitor \
    Generic_Join_Devel:Generic_Join \
    MFODL_Monitor_Devel:MFODL_Monitor_Optimized"

if [[ -n $1 ]]; then
    AFP="$1"
else
    ISABELLE="${ISABELLE:-isabelle}"
    AFP="$("$ISABELLE" getenv -b AFP)"
fi
if [[ -d $AFP ]]; then
    echo "AFP = $AFP"
else
    echo "Error: could not find AFP"
    exit 1
fi

SED_SCRIPT=""
for session in $SESSIONS; do
    src=${session%:*}
    dst=${session#*:}
    SED_SCRIPT="${SED_SCRIPT}s/$src/$dst/g;"
done

for session in $SESSIONS; do
    src=${session%:*}
    dst=${session#*:}
    echo "Copying $src to $dst ..."

    rm -r "$AFP/$dst"
    cp -r "$src" "$AFP/$dst"
    find "$AFP/$dst" \( -name '*~' -o -name '*.ocaml' \) -delete
    find "$AFP/$dst" \( -name ROOT -o -name '*.thy' \) -exec sed -i "$SED_SCRIPT" \{\} \;
done
echo "Done."
