  $ echo 'ONCE[5,5] 1=1' > test13_1.mfotl
  $ monpoly -verified -sig test13.sig -formula test13_1.mfotl -log test13.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[5,5] 1 = 1
  The sequence of free variables is: ()
  At time point 0:
  @0 (time point 0): false
  At time point 1:
  @5 (time point 1): true
  At time point 2:
  @6 (time point 2): false
