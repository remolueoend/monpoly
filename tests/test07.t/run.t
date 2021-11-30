  $ echo 'EVENTUALLY[0,60] (1=0)' > test7_1.mfotl
  $ monpoly -sig test7.sig -formula test7_1.mfotl -log test7.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,60] 1 = 0
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @100 (time point 0): false
  @100 (time point 1): false
  @100 (time point 2): false
  @100 (time point 3): false
