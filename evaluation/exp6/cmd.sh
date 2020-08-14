f=$(echo $1 | cut -d "_" -f3)
log=$(echo $1 | cut -d "_" -f1-7)
er=$(echo $1 | cut -d "_" -f4)
fma="${f}.mdl"
sig="${f}.sig"

echo "aerial -fmla fmas/$fma -log logs/$log -mode naive | sed  '/^[A-Z]/d' | grep false | sort -n"

echo "hydra fmas/$fma logs/$log | sed  '/^[A-Z]/d'"

echo "verimon -no_rw -nofilteremptytp -nofilterrel -sig fmas/$sig -formula fmas/$fma -log logs/$log -negate -verified | sed 's/@//g;s/. (time point /:/g;s/)://g;s/ true/:false/g' | awk -F':' -v d=${er} '{print \$1,(\$2 % d),\$3}' OFS=':' | sed 's/:false/ false/g'"
