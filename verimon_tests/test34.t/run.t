  $ echo 'S(y) AND ((NOT P(y) AND Q(x)) SINCE[10,12] R(x,y))' > test34_1.mfotl
  $ monpoly -verified -sig test34.sig -formula test34_1.mfotl -log test34.log
  @10 (time point 2): (2,1)
