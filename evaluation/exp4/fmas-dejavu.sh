ls reports/ | grep diff | grep dejavu | cut -d"_" -f3 | uniq | xargs -I J cat fmas/J.qtl
