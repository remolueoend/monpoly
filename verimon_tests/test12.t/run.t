  $ echo 'P(x) SINCE[5,5] Q(x)' > test12_1.mfotl
  $ monpoly -verified -sig test12.sig -formula test12_1.mfotl -log test12.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) SINCE[5,5] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @5 (time point 1): ((111))
  At time point 2:
  @6 (time point 2): ()
