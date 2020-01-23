ls reports/ | grep diff | grep monpoly | cut -d"_" -f3 | uniq | xargs -I J cat fmas/J_future.mfotl
