  $ echo '(x1 <- MAX x1; x2 (ONCE[1,1] (S(y1,x1,x2))))' > test30_1.mfotl
  $ monpoly -verified -sig test30.sig -formula test30_1.mfotl -log test30.log -verbose -nonewlastts
  The analyzed formula is:
    x1 <- MAX x1; x2 ONCE[1,1] S(y1,x1,x2)
  The sequence of free variables is: (x1,x2)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ((7,2))
  At time point 2:
  @2 (time point 2): ((6,3))
