  $ echo 'S(x2,x1,x3) OR trans(x3,x2,x1)' > test27_1.mfotl
  $ monpoly -sig test27.sig -formula test27_1.mfotl -log test27.log -verbose -nonewlastts
  The analyzed formula is:
    S(x2,x1,x3) OR trans(x3,x2,x1)
  The sequence of free variables is: (x2,x1,x3)
  At time point 0:
  @0 (time point 0): ((1,2,3))
  At time point 1:
  @1 (time point 1): ((2,3,1))
