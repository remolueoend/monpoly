f=$(echo $1 | cut -d "_" -f3)
log=$(echo $1 | cut -d "_" -f1-7)
fma="${f}_future.mfotl"
sig="${f}_future.sig"
fmad="${f}.mfotl"
sigd="${f}.sig"

echo "monpoly -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log"

echo "verimon -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log -verified"

echo "dejavu-run fmas/$f logs/$log ./output"

echo "verimon -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sigd -formula fmas/$fmad -log logs/$log -verified"
