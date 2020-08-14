f=$(echo $1 | cut -d "_" -f3)
log=$(echo $1 | cut -d "_" -f1-7)
fma="${f}.mfotl"
sig="${f}.sig"

echo "monpoly -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log"

echo "verimon -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log"

echo "verimon-old -no_rw -nonewlastts -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log"

echo "aerial -fmla fmas/$fma -log logs/$log -mode naive | sed  '/^[A-Z]/d' | grep false"

echo "hydra fmas/$fma logs/$log | sed  '/^[A-Z]/d'"
