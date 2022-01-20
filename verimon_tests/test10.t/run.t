  $ echo 'EVENTUALLY [0,0] P(x)' > test10_1.mfotl
  $ monpoly -verified -sig test10.sig -formula test10_1.mfotl -log test10.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,0] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @110 (time point 0): ((5))
  At time point 2:
  @120 (time point 1): ()
