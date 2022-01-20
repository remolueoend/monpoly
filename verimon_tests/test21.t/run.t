  $ echo 'NOT b(x) UNTIL [0,5] c(x)' > test21_1.mfotl
  $ monpoly -verified -sig test21.sig -formula test21_1.mfotl -log test21.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT b(x)) UNTIL[0,5] c(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  At time point 5:
  At time point 6:
  @0 (time point 0): ((13))
  At time point 7:
  @1 (time point 1): ((13),(14))
  @2 (time point 2): ((10),(13),(14))
  @3 (time point 3): ((11),(13),(14))
  @4 (time point 4): ((11),(12),(13),(14))
  @5 (time point 5): ((10),(11),(14))
  @6 (time point 6): ((11),(14))
