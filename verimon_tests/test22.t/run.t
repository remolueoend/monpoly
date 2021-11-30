  $ echo 'p(x) SINCE q(y,x)' > test22_1.mfotl
  $ monpoly -verified -sig test22.sig -formula test22_1.mfotl -log test22.log -verbose -nonewlastts
  The analyzed formula is:
    p(x) SINCE[0,*) q(y,x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @0 (time point 0): ((1,2),(1,3))
  At time point 1:
  @1 (time point 1): ((1,3))
