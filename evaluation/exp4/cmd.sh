f=$(echo $1 | cut -d "_" -f3)
log=$(echo $1 | cut -d "_" -f1-7)
fma="${f}_future.mfotl"
sig="${f}_future.sig"

echo "monpoly-legacy -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log"

echo "monpoly -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log -verified"

