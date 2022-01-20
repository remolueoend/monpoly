  $ echo 'EVENTUALLY[0,10] p(x)' > test15_1.mfotl
  $ monpoly -sig test15.sig -formula test15_1.mfotl -log test15.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((0),(1),(2),(3))
  @11 (time point 1): ((1),(2),(3))
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo 'EVENTUALLY[1,10] p(x)' > test15_2.mfotl
  $ monpoly -sig test15.sig -formula test15_2.mfotl -log test15.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((2),(3))
  @11 (time point 1): ((2),(3))
  @14 (time point 2): ()
  @14 (time point 3): ()

  $ echo 'EVENTUALLY[0,2] p(x)' > test15_3.mfotl
  $ monpoly -sig test15.sig -formula test15_3.mfotl -log test15.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ((0),(1))
  @11 (time point 1): ((1))
  At time point 3:
  At time point 4:
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo 'EVENTUALLY[1,2] p(x)' > test15_4.mfotl
  $ monpoly -sig test15.sig -formula test15_4.mfotl -log test15.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ()
  @11 (time point 1): ()
  At time point 3:
  At time point 4:
  @14 (time point 2): ()
  @14 (time point 3): ()
