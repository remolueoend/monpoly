#!/bin/bash


egrep -ar "." ./reports/  | sed 's/_/ /g' | sort -n -k4  | cut -d " " -f4 | sort -n | uniq > rates.tbl

egrep -ar "." ./reports/ | grep multiway | sed 's/_/ /g' | sort -n -k4  |  grep monpoly | cut -d ":" -f2 > multiway_monpoly.tbl
egrep -ar "." ./reports/ | grep multiway | sed 's/_/ /g' | sort -n -k4  |  grep verimon: | cut -d ":" -f2 > multiway_verimon.tbl
egrep -ar "." ./reports/ | grep multiway | sed 's/_/ /g' | sort -n -k4  | grep verimon-old | cut -d ":" -f2 > multiway_verimon-old.tbl

egrep -ar "." ./reports/ | grep sliding | sed 's/_/ /g' | sort -n -k4  | grep monpoly | cut -d ":" -f2 > sliding_monpoly.tbl
egrep -ar "." ./reports/ | grep sliding | sed 's/_/ /g' | sort -n -k4  | grep verimon: | cut -d ":" -f2 > sliding_verimon.tbl
egrep -ar "." ./reports/ | grep sliding | sed 's/_/ /g' | sort -n -k4  | grep verimon-old | cut -d ":" -f2 > sliding_verimon-old.tbl

egrep -ar "." ./reports/ | grep aggr | sed 's/_/ /g' | sort -n -k4  | grep monpoly | cut -d ":" -f2 > aggr_monpoly.tbl
egrep -ar "." ./reports/ | grep aggr | sed 's/_/ /g' | sort -n -k4  | grep verimon: | cut -d ":" -f2 > aggr_verimon.tbl

egrep -ar "." ./reports/ | grep regex | sed 's/_/ /g' | sort -n -k4  | grep aerial | cut -d ":" -f2 > regex_aerial.tbl
egrep -ar "." ./reports/ | grep regex | sed 's/_/ /g' | sort -n -k4  | grep hydra  | cut -d ":" -f2> regex_hydra.tbl
egrep -ar "." ./reports/ | grep regex | sed 's/_/ /g' | sort -n -k4  | grep verimon  | cut -d ":" -f2 > regex_verimon.tbl


pr -mts',' rates.tbl multiway_monpoly.tbl multiway_verimon.tbl multiway_verimon-old.tbl sliding_monpoly.tbl sliding_verimon.tbl sliding_verimon-old.tbl aggr_monpoly.tbl aggr_verimon.tbl regex_aerial.tbl regex_hydra.tbl regex_verimon.tbl  > table.txt

rm *.tbl
