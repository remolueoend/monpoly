  $ echo '(r <- CNT x;x ONCE (W(x) AND ONCE I(y))) AND t = i2f(r)' > test31_1.mfotl
  $ monpoly -verified -sig test31.sig -formula test31_1.mfotl -log test31.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x; x ONCE[0,*) (W(x) AND (ONCE[0,*) I(y)))) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ((2,"no",2),(2,"yes",2))
