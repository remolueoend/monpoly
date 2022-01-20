  $ echo '(NOT EVENTUALLY[0,3] T()) UNTIL[0,1] U()' > test26_1.mfotl
  $ monpoly -sig test26.sig -formula test26_1.mfotl -log test26.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT EVENTUALLY[0,3] T()) UNTIL[0,1] U()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  At time point 5:
  @10 (time point 0): true
  At time point 6:
  @11 (time point 1): true
  At time point 7:
  @12 (time point 2): true
  At time point 8:
  @13 (time point 3): true
  At time point 9:
  @14 (time point 4): true
